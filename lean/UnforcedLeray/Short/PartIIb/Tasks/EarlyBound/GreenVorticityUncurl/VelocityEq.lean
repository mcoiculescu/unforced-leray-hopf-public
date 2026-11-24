import UnforcedLeray.Short.PartIIb.Tasks.EarlyBound.GreenVorticityUncurl.Needed
import UnforcedLeray.Short.PartIIb.Tasks.GlobalEnergy.TailSourceSlice.PeriodizeTest
import UnforcedLeray.Short.PartI.Tasks.TrainClass.FluctStreamSmooth.Prim
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.MeanValue

/-!
# `PartII-b:F6/2/3`: Forced Coupled Vorticity to Meridional Velocity Equation (`VelocityEq`)

Source of record: `the November 2 reference manuscript` (SP), lines 2216–2222,
2258–2268.

Proves `UnforcedLeray.Short.IIb.GreenVorticityUncurlNeeded.greenVorticityToVelocityEq_proof :
UnforcedLeray.Short.IIb.GreenVorticityUncurlNeeded.GreenVorticityToVelocityEq` unconditionally:
1. Constructs the compactly supported smooth scalar stream potential `Φ` (`IsCoordTest Φ`,
   `tsupport Φ ⊆ Ioo 0 p.H ×ˢ univ`) of any planar solenoidal test `Ψ` supported in
   `Ioo 0 p.H ×ˢ univ`, satisfying `Ψ = (∂_η Φ, -∂_q Φ)`;
2. Periodizes `Φ` in `q` to `φ(s) = qPeriodize p.c Φ s` (`φ(0) = φ(p.H) = 0`) and passes from
   constant-in-time cylinder tests in `hom_weak` to `φ(s)` via uniform Riemann-sum time-stepping on
   `[0, p.H]`;
3. Identifies the slice pairings of `z · meridTranspose p.ν Ψ`, `cdot (flatBv p.train z zq zη) Ψ`,
   and `cdot g Ψ` with `-∫_cell om ∂_s φ - ∫_cell cylCoupledIntegrand(om, φ)` and `∫_cell f φ` via
   `TailPeriodizeAux.integrable_and_integral_coord_eq_cell_qPeriodize`, `IsBiotSavart`,
   `HasWeakCellDerivC`, and `HasWeakVec`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff Interval

namespace UnforcedLeray.Short.IIb.GreenVorticityUncurlNeeded

namespace VelocityEqAux

open UnforcedLeray UnforcedLeray.Short.IIb UnforcedLeray.Short.IIb.TailPeriodizeAux
open UnforcedLeray.Cons.C03.Concrete

private theorem int_add {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} {f g : α → E} (hf : Integrable f μ) (hg : Integrable g μ) :
    Integrable (fun x => f x + g x) μ :=
  hf.add hg

private theorem intOn_add {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} {s : Set α} {f g : α → E}
    (hf : IntegrableOn f s μ) (hg : IntegrableOn g s μ) :
    IntegrableOn (fun x => f x + g x) s μ :=
  hf.add hg

private theorem intOn_sub {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} {s : Set α} {f g : α → E}
    (hf : IntegrableOn f s μ) (hg : IntegrableOn g s μ) :
    IntegrableOn (fun x => f x - g x) s μ :=
  hf.sub hg

private theorem intOn_neg {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} {s : Set α} {f : α → E}
    (hf : IntegrableOn f s μ) :
    IntegrableOn (fun x => -f x) s μ :=
  hf.neg

/-! ## 1. Scalar stream potential `Φ` for `IsPlanarSolTest Ψ` on `(0, H) × ℝ²` -/

private theorem planarSolTest_box {H : ℝ} (hH : 0 < H) {Ψ : Coord → Fin 2 → ℝ}
    (hΨ : IsPlanarSolTest Ψ)
    (hsupp : ∀ i : Fin 2, tsupport (fun x => Ψ x i) ⊆ Ioo 0 H ×ˢ univ) :
    ∃ a b R : ℝ, 0 < a ∧ a ≤ b ∧ b < H ∧ 0 < R ∧
      ∀ (i : Fin 2) (x : Coord),
        (x.1 ∉ Icc a b ∨ R < |x.2.1| ∨ R < |x.2.2|) →
          x ∉ tsupport (fun y => Ψ y i) := by
  let S : Set Coord := tsupport (fun x => Ψ x 0) ∪ tsupport (fun x => Ψ x 1)
  have hS_comp : IsCompact S := (hΨ.smooth 0).compact.union (hΨ.smooth 1).compact
  have hS_sub : S ⊆ Ioo 0 H ×ˢ univ := union_subset (hsupp 0) (hsupp 1)
  obtain ⟨M, hM⟩ := hS_comp.isBounded.subset_closedBall (0 : Coord)
  let R : ℝ := max 1 M
  have hR_pos : 0 < R := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hR_mem : ∀ x ∈ S, |x.2.1| ≤ R ∧ |x.2.2| ≤ R := by
    intro x hx
    have hxM : ‖x‖ ≤ M := by simpa [Metric.mem_closedBall, dist_zero_right] using hM hx
    have hxR : ‖x‖ ≤ R := hxM.trans (le_max_right _ _)
    have h2 : ‖x.2‖ ≤ ‖x‖ := norm_snd_le x
    exact ⟨Real.norm_eq_abs x.2.1 ▸ (norm_fst_le x.2).trans (h2.trans hxR),
      Real.norm_eq_abs x.2.2 ▸ (norm_snd_le x.2).trans (h2.trans hxR)⟩
  have hmem_S : ∀ (i : Fin 2) {x : Coord}, x ∈ tsupport (fun y => Ψ y i) → x ∈ S := by
    intro i x hx
    fin_cases i
    · exact Or.inl hx
    · exact Or.inr hx
  by_cases hne : S.Nonempty
  · let K₁ : Set ℝ := Prod.fst '' S
    have hK₁_comp : IsCompact K₁ := hS_comp.image continuous_fst
    have hK₁_ne : K₁.Nonempty := hne.image Prod.fst
    let a : ℝ := sInf K₁
    let b : ℝ := sSup K₁
    obtain ⟨x₀, hx₀, hx₀_eq⟩ := hK₁_comp.sInf_mem hK₁_ne
    obtain ⟨x₁, hx₁, hx₁_eq⟩ := hK₁_comp.sSup_mem hK₁_ne
    have ha_pos : 0 < a := by dsimp [a]; rw [← hx₀_eq]; exact (hS_sub hx₀).1.1
    have hb_lt : b < H := by dsimp [b]; rw [← hx₁_eq]; exact (hS_sub hx₁).1.2
    have hab : a ≤ b :=
      (csInf_le hK₁_comp.bddBelow ⟨x₀, hx₀, rfl⟩).trans (le_csSup hK₁_comp.bddAbove ⟨x₀, hx₀, rfl⟩)
    refine ⟨a, b, R, ha_pos, hab, hb_lt, hR_pos, fun i x hx hxt => ?_⟩
    have hxS : x ∈ S := hmem_S i hxt
    have hx1 : x.1 ∈ K₁ := ⟨x, hxS, rfl⟩
    have hx_ab : x.1 ∈ Icc a b := ⟨csInf_le hK₁_comp.bddBelow hx1, le_csSup hK₁_comp.bddAbove hx1⟩
    obtain ⟨hqR, hηR⟩ := hR_mem x hxS
    rcases hx with h1 | h2 | h3
    · exact h1 hx_ab
    · linarith
    · linarith
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    refine ⟨H / 2, H / 2, R, half_pos hH, le_rfl, half_lt_self hH, hR_pos, fun i x _ hxt => ?_⟩
    have hxS : x ∈ S := hmem_S i hxt
    rw [hne] at hxS
    exact hxS

private def streamPot (R : ℝ) (Ψ : Coord → Fin 2 → ℝ) (x : Coord) : ℝ :=
  -∫ τ in (-R - 1)..x.2.1, Ψ (x.1, (τ, x.2.2)) 1

private theorem contDiff_streamPot (R : ℝ) {Ψ : Coord → Fin 2 → ℝ}
    (hΨ1 : ContDiff ℝ ∞ (fun x => Ψ x 1)) :
    ContDiff ℝ ∞ (streamPot R Ψ) := by
  let q₀ : ℝ := -R - 1
  let Hfun : ℝ × Coord → ℝ := fun p =>
    Ψ (p.2.1, (q₀ + (p.2.2.1 - q₀) * p.1, p.2.2.2)) 1
  have hH_sm : ContDiff ℝ ∞ Hfun := by
    refine hΨ1.comp ?_
    exact (contDiff_fst.comp contDiff_snd).prodMk
      ((contDiff_const.add (((contDiff_fst.comp (contDiff_snd.comp contDiff_snd)).sub
        contDiff_const).mul contDiff_fst)).prodMk
        (contDiff_snd.comp (contDiff_snd.comp contDiff_snd)))
  have hprim : ContDiff ℝ ∞ (fun x : Coord => ∫ τ in (0 : ℝ)..1, Hfun (τ, x)) :=
    UnforcedLeray.Short.PartI.FluctPrim.contDiff_primitive01 hH_sm
  have heq : streamPot R Ψ =
      fun x : Coord => -((x.2.1 - q₀) * ∫ τ in (0 : ℝ)..1, Hfun (τ, x)) := by
    funext x
    unfold streamPot
    congr 1
    have h1 := intervalIntegral.smul_integral_comp_add_mul
      (f := fun τ => Ψ (x.1, (τ, x.2.2)) 1) (a := (0 : ℝ)) (b := 1) (x.2.1 - q₀) q₀
    simpa [Hfun, q₀, smul_eq_mul] using h1.symm
  rw [heq]
  exact (((contDiff_fst.comp contDiff_snd).sub contDiff_const).mul hprim).neg

private theorem hasDerivAt_coord_line {g : Coord → ℝ} (hg : ContDiff ℝ ∞ g)
    (j : Fin 3) (x : Coord) :
    HasDerivAt (fun t : ℝ => g (x + t • cdir j)) (cpd j g x) 0 := by
  have h1 : HasFDerivAt g (fderiv ℝ g x) (x + (0 : ℝ) • cdir j) := by
    simpa using (hg.differentiable (by simp) x).hasFDerivAt
  have h2 : HasDerivAt (fun t : ℝ => x + t • cdir j) (cdir j) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (cdir j)).const_add x
  simpa [cpd, Function.comp_def] using h1.comp_hasDerivAt 0 h2

private theorem hasDerivAt_coord_shift {g : Coord → ℝ} (hg : ContDiff ℝ ∞ g)
    (j : Fin 3) (x : Coord) (s₀ : ℝ) :
    HasDerivAt (fun s : ℝ => g (x + (s - s₀) • cdir j)) (cpd j g x) s₀ := by
  let γ : ℝ → Coord := fun s => x + (s - s₀) • cdir j
  have h1 : HasFDerivAt g (fderiv ℝ g x) (γ s₀) := by
    dsimp [γ]
    rw [sub_self, zero_smul, add_zero]
    exact (hg.differentiable (by simp) x).hasFDerivAt
  have h2 : HasDerivAt γ (cdir j) s₀ := by
    dsimp [γ]
    exact (((hasDerivAt_id' s₀).sub_const s₀).smul_const (cdir j)).const_add x |>.congr_deriv
      (one_smul ℝ (cdir j))
  exact h1.comp_hasDerivAt s₀ h2

private theorem cpd1_streamPot (R : ℝ) {Ψ : Coord → Fin 2 → ℝ} (hΨ : IsPlanarSolTest Ψ)
    (x : Coord) :
    cpd 1 (streamPot R Ψ) x = -Ψ x 1 := by
  have hΦ_sm : ContDiff ℝ ∞ (streamPot R Ψ) := contDiff_streamPot R (hΨ.smooth 1).smooth
  have hd1 := hasDerivAt_coord_line hΦ_sm 1 x
  have hcont : Continuous (fun τ : ℝ => Ψ (x.1, (τ, x.2.2)) 1) :=
    (hΨ.smooth 1).smooth.continuous.comp
      (continuous_const.prodMk (continuous_id.prodMk continuous_const))
  have hftc : HasDerivAt (fun q : ℝ => ∫ τ in (-R - 1)..q, Ψ (x.1, (τ, x.2.2)) 1)
      (Ψ (x.1, (x.2.1, x.2.2)) 1) x.2.1 :=
    intervalIntegral.integral_hasDerivAt_right (hcont.intervalIntegrable _ _)
      (hcont.stronglyMeasurableAtFilter _ _) hcont.continuousAt
  have hline : (fun t : ℝ => streamPot R Ψ (x + t • cdir 1)) =
      fun t : ℝ => -∫ τ in (-R - 1)..(x.2.1 + t), Ψ (x.1, (τ, x.2.2)) 1 := by
    funext t
    simp [streamPot, cdir]
  have hd2 : HasDerivAt (fun t : ℝ => streamPot R Ψ (x + t • cdir 1)) (-Ψ x 1) 0 := by
    rw [hline]
    let sh : ℝ → ℝ := fun t => x.2.1 + t
    have hsh : HasDerivAt sh 1 0 := (hasDerivAt_id' (0 : ℝ)).const_add x.2.1
    have hftc' : HasDerivAt (fun q : ℝ => ∫ τ in (-R - 1)..q, Ψ (x.1, (τ, x.2.2)) 1)
        (Ψ x 1) (sh 0) := by
      dsimp [sh]; rw [add_zero]; exact hftc
    exact ((hftc'.comp (0 : ℝ) hsh).congr_deriv (mul_one _)).fun_neg
  exact hd1.unique hd2

private theorem hasDerivAt_integral_eta {Ψ1 : Coord → ℝ} (hΨ1 : ContDiff ℝ ∞ Ψ1)
    (s q₀ q₁ η₀ : ℝ) :
    HasDerivAt (fun η : ℝ => ∫ τ in q₀..q₁, Ψ1 (s, (τ, η)))
      (∫ τ in q₀..q₁, cpd 2 Ψ1 (s, (τ, η₀))) η₀ := by
  let F : ℝ → ℝ → ℝ := fun η τ => Ψ1 (s, (τ, η))
  let F' : ℝ → ℝ → ℝ := fun η τ => cpd 2 Ψ1 (s, (τ, η))
  have hF'_sm : ContDiff ℝ ∞ (cpd 2 Ψ1) :=
    (ContDiff.fderiv_right (m := ∞) hΨ1 (by simp)).clm_apply contDiff_const
  let K : Set Coord := {s} ×ˢ (uIcc q₀ q₁ ×ˢ Metric.closedBall η₀ 1)
  have hK : IsCompact K := isCompact_singleton.prod (isCompact_uIcc.prod (isCompact_closedBall η₀ 1))
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hF'_sm.continuous.continuousOn
  have hs_nhds : Metric.ball η₀ 1 ∈ 𝓝 η₀ := Metric.ball_mem_nhds η₀ one_pos
  have hF_meas : ∀ᶠ η in 𝓝 η₀, AEStronglyMeasurable (F η) (volume.restrict (Ι q₀ q₁)) := by
    refine Eventually.of_forall fun η => ?_
    exact (hΨ1.continuous.comp
      (continuous_const.prodMk (continuous_id.prodMk continuous_const))).aestronglyMeasurable
  have hF_int : IntervalIntegrable (F η₀) volume q₀ q₁ :=
    (hΨ1.continuous.comp
      (continuous_const.prodMk (continuous_id.prodMk continuous_const))).intervalIntegrable _ _
  have hF'_meas : AEStronglyMeasurable (F' η₀) (volume.restrict (Ι q₀ q₁)) :=
    (hF'_sm.continuous.comp
      (continuous_const.prodMk (continuous_id.prodMk continuous_const))).aestronglyMeasurable
  have h_bound : ∀ᵐ τ ∂volume, τ ∈ Ι q₀ q₁ → ∀ η ∈ Metric.ball η₀ 1, ‖F' η τ‖ ≤ C := by
    refine Eventually.of_forall fun τ hτ η hη => ?_
    exact hC (s, (τ, η)) ⟨rfl, uIoc_subset_uIcc hτ, Metric.ball_subset_closedBall hη⟩
  have h_diff : ∀ᵐ τ ∂volume, τ ∈ Ι q₀ q₁ → ∀ η ∈ Metric.ball η₀ 1,
      HasDerivAt (fun η' => F η' τ) (F' η τ) η := by
    refine Eventually.of_forall fun τ _ η _ => ?_
    have h := hasDerivAt_coord_shift hΨ1 2 (s, (τ, η)) η
    exact h.congr_of_eventuallyEq (Eventually.of_forall fun η' => by simp [F, cdir])
  exact (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le hs_nhds
    hF_meas hF_int hF'_meas h_bound intervalIntegrable_const h_diff).2

private theorem cpd2_streamPot {R : ℝ} (hR : 0 < R) {Ψ : Coord → Fin 2 → ℝ}
    (hΨ : IsPlanarSolTest Ψ)
    (hsupp0 : ∀ x : Coord, R < |x.2.1| → Ψ x 0 = 0) (x : Coord) :
    cpd 2 (streamPot R Ψ) x = Ψ x 0 := by
  have hΦ_sm : ContDiff ℝ ∞ (streamPot R Ψ) := contDiff_streamPot R (hΨ.smooth 1).smooth
  have hd1 := hasDerivAt_coord_line hΦ_sm 2 x
  have hd_eta := hasDerivAt_integral_eta (hΨ.smooth 1).smooth x.1 (-R - 1) x.2.1 x.2.2
  have hline : (fun t : ℝ => streamPot R Ψ (x + t • cdir 2)) =
      fun t : ℝ => -∫ τ in (-R - 1)..x.2.1, Ψ (x.1, (τ, x.2.2 + t)) 1 := by
    funext t
    simp [streamPot, cdir]
  have hd2 : HasDerivAt (fun t : ℝ => streamPot R Ψ (x + t • cdir 2))
      (-∫ τ in (-R - 1)..x.2.1, cpd 2 (fun y => Ψ y 1) (x.1, (τ, x.2.2))) 0 := by
    rw [hline]
    let sh : ℝ → ℝ := fun t => x.2.2 + t
    have hsh : HasDerivAt sh 1 0 := (hasDerivAt_id' (0 : ℝ)).const_add x.2.2
    have hd_eta' : HasDerivAt (fun η : ℝ => ∫ τ in (-R - 1)..x.2.1, Ψ (x.1, (τ, η)) 1)
        (∫ τ in (-R - 1)..x.2.1, cpd 2 (fun y => Ψ y 1) (x.1, (τ, x.2.2))) (sh 0) := by
      dsimp [sh]; rw [add_zero]; exact hd_eta
    exact ((hd_eta'.comp (0 : ℝ) hsh).congr_deriv (mul_one _)).fun_neg
  have heq_int : -∫ τ in (-R - 1)..x.2.1, cpd 2 (fun y => Ψ y 1) (x.1, (τ, x.2.2)) = Ψ x 0 := by
    have hdiv : (fun τ : ℝ => -cpd 2 (fun y => Ψ y 1) (x.1, (τ, x.2.2))) =
        fun τ : ℝ => cpd 1 (fun y => Ψ y 0) (x.1, (τ, x.2.2)) := by
      funext τ
      linarith [hΨ.div_free (x.1, (τ, x.2.2))]
    rw [← intervalIntegral.integral_neg]
    simp_rw [hdiv]
    have h_deriv_q : ∀ τ ∈ uIcc (-R - 1) x.2.1,
        HasDerivAt (fun q : ℝ => Ψ (x.1, (q, x.2.2)) 0)
          (cpd 1 (fun y => Ψ y 0) (x.1, (τ, x.2.2))) τ := by
      intro τ _
      have h := hasDerivAt_coord_shift (hΨ.smooth 0).smooth 1 (x.1, (τ, x.2.2)) τ
      exact h.congr_of_eventuallyEq (Eventually.of_forall fun q => by simp [cdir])
    have hcont_d : Continuous (fun τ : ℝ => cpd 1 (fun y => Ψ y 0) (x.1, (τ, x.2.2))) := by
      have hsm : ContDiff ℝ ∞ (cpd 1 (fun y => Ψ y 0)) :=
        (ContDiff.fderiv_right (m := ∞) (hΨ.smooth 0).smooth (by simp)).clm_apply contDiff_const
      exact hsm.continuous.comp (continuous_const.prodMk (continuous_id.prodMk continuous_const))
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt h_deriv_q (hcont_d.intervalIntegrable _ _)]
    have hvan : Ψ (x.1, (-R - 1, x.2.2)) 0 = 0 := by
      apply hsupp0
      dsimp
      rw [abs_of_neg (by linarith)]
      linarith
    rw [hvan, sub_zero]
  rw [← heq_int]
  exact hd1.unique hd2

private theorem full_integral_Ψ1_eq_zero {R : ℝ} (hR : 0 < R) {Ψ : Coord → Fin 2 → ℝ}
    (hΨ : IsPlanarSolTest Ψ)
    (hsupp0 : ∀ x : Coord, R < |x.2.1| → Ψ x 0 = 0)
    (hsupp1 : ∀ x : Coord, R < |x.2.2| → Ψ x 1 = 0)
    (s η : ℝ) :
    ∫ τ in (-R - 1)..(R + 1), Ψ (s, (τ, η)) 1 = 0 := by
  let g : ℝ → ℝ := fun η' => ∫ τ in (-R - 1)..(R + 1), Ψ (s, (τ, η')) 1
  have hg_deriv : ∀ η' : ℝ, HasDerivAt g 0 η' := by
    intro η'
    have hd := hasDerivAt_integral_eta (hΨ.smooth 1).smooth s (-R - 1) (R + 1) η'
    have hzero : ∫ τ in (-R - 1)..(R + 1), cpd 2 (fun y => Ψ y 1) (s, (τ, η')) = 0 := by
      have hdiv : (fun τ : ℝ => cpd 2 (fun y => Ψ y 1) (s, (τ, η'))) =
          fun τ : ℝ => -cpd 1 (fun y => Ψ y 0) (s, (τ, η')) := by
        funext τ
        linarith [hΨ.div_free (s, (τ, η'))]
      simp_rw [hdiv]
      rw [intervalIntegral.integral_neg]
      have h_deriv_q : ∀ τ ∈ uIcc (-R - 1) (R + 1),
          HasDerivAt (fun q : ℝ => Ψ (s, (q, η')) 0)
            (cpd 1 (fun y => Ψ y 0) (s, (τ, η'))) τ := by
        intro τ _
        have h := hasDerivAt_coord_shift (hΨ.smooth 0).smooth 1 (s, (τ, η')) τ
        exact h.congr_of_eventuallyEq (Eventually.of_forall fun q => by simp [cdir])
      have hcont_d : Continuous (fun τ : ℝ => cpd 1 (fun y => Ψ y 0) (s, (τ, η'))) := by
        have hsm : ContDiff ℝ ∞ (cpd 1 (fun y => Ψ y 0)) :=
          (ContDiff.fderiv_right (m := ∞) (hΨ.smooth 0).smooth (by simp)).clm_apply contDiff_const
        exact hsm.continuous.comp (continuous_const.prodMk (continuous_id.prodMk continuous_const))
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt h_deriv_q (hcont_d.intervalIntegrable _ _)]
      have hv1 : Ψ (s, (R + 1, η')) 0 = 0 := by
        apply hsupp0; dsimp; rw [abs_of_pos (by linarith)]; linarith
      have hv0 : Ψ (s, (-R - 1, η')) 0 = 0 := by
        apply hsupp0; dsimp; rw [abs_of_neg (by linarith)]; linarith
      simp [hv1, hv0]
    rwa [hzero] at hd
  have hg_const : g η = g (R + 1) :=
    is_const_of_deriv_eq_zero (fun y => (hg_deriv y).differentiableAt)
      (fun y => (hg_deriv y).deriv) η (R + 1)
  have hg_R1 : g (R + 1) = 0 := by
    dsimp [g]
    have h0 : (fun τ : ℝ => Ψ (s, (τ, R + 1)) 1) = fun _ => 0 := by
      funext τ
      apply hsupp1
      dsimp
      rw [abs_of_pos (by linarith)]
      linarith
    simp [h0]
  exact hg_const.trans hg_R1

private theorem streamPot_eq_zero_outside {a b R : ℝ} (hR : 0 < R)
    {Ψ : Coord → Fin 2 → ℝ} (hΨ : IsPlanarSolTest Ψ)
    (hbox : ∀ (i : Fin 2) (x : Coord),
      (x.1 ∉ Icc a b ∨ R < |x.2.1| ∨ R < |x.2.2|) → x ∉ tsupport (fun y => Ψ y i))
    {x : Coord} (hx : x.1 ∉ Icc a b ∨ R < |x.2.1| ∨ R < |x.2.2|) :
    streamPot R Ψ x = 0 := by
  have hvan : ∀ (i : Fin 2) (y : Coord),
      (y.1 ∉ Icc a b ∨ R < |y.2.1| ∨ R < |y.2.2|) → Ψ y i = 0 :=
    fun i y hy => image_eq_zero_of_notMem_tsupport (f := fun z => Ψ z i) (hbox i y hy)
  rcases hx with hs | hq | hη
  · unfold streamPot
    have h0 : (fun τ : ℝ => Ψ (x.1, (τ, x.2.2)) 1) = fun _ => 0 :=
      funext fun τ => hvan 1 (x.1, (τ, x.2.2)) (Or.inl hs)
    simp [h0]
  · unfold streamPot
    rcases lt_or_gt_of_ne (by intro heq; rw [heq, abs_of_pos hR] at hq; exact lt_irrefl R hq : x.2.1 ≠ R)
        with hlt | hgt
    · have hq_neg : x.2.1 < -R := by
        by_contra hge
        push Not at hge
        exact absurd (abs_le.2 ⟨hge, hlt.le⟩) (not_le.2 hq)
      have h0 : EqOn (fun τ : ℝ => Ψ (x.1, (τ, x.2.2)) 1) 0 (uIcc (-R - 1) x.2.1) := by
        intro τ hτ
        have hτ_le : τ ≤ max (-R - 1) x.2.1 := hτ.2
        have hτ_lt : τ < -R := lt_of_le_of_lt hτ_le (max_lt (by linarith) hq_neg)
        exact hvan 1 (x.1, (τ, x.2.2)) (Or.inr (Or.inl (by dsimp; rw [abs_of_neg (by linarith)]; linarith)))
      rw [intervalIntegral.integral_congr h0]
      simp
    · have hcont1 : Continuous (fun τ : ℝ => Ψ (x.1, (τ, x.2.2)) 1) :=
        (hΨ.smooth 1).smooth.continuous.comp
          (continuous_const.prodMk (continuous_id.prodMk continuous_const))
      rw [← intervalIntegral.integral_add_adjacent_intervals
        (b := R + 1) (hcont1.intervalIntegrable _ _) (hcont1.intervalIntegrable _ _)]
      have hfull := full_integral_Ψ1_eq_zero hR hΨ
        (fun y hy => hvan 0 y (Or.inr (Or.inl hy)))
        (fun y hy => hvan 1 y (Or.inr (Or.inr hy))) x.1 x.2.2
      have htail : ∫ τ in (R + 1)..x.2.1, Ψ (x.1, (τ, x.2.2)) 1 = 0 := by
        have h0 : EqOn (fun τ : ℝ => Ψ (x.1, (τ, x.2.2)) 1) 0 (uIcc (R + 1) x.2.1) := by
          intro τ hτ
          have hτ_ge : min (R + 1) x.2.1 ≤ τ := hτ.1
          have hτ_gt : R < τ := lt_of_lt_of_le (lt_min (by linarith) hgt) hτ_ge
          exact hvan 1 (x.1, (τ, x.2.2))
            (Or.inr (Or.inl (by dsimp; rw [abs_of_pos (lt_trans hR hτ_gt)]; exact hτ_gt)))
        rw [intervalIntegral.integral_congr h0]
        simp
      rw [hfull, htail, add_zero, neg_zero]
  · unfold streamPot
    have h0 : (fun τ : ℝ => Ψ (x.1, (τ, x.2.2)) 1) = fun _ => 0 :=
      funext fun τ => hvan 1 (x.1, (τ, x.2.2)) (Or.inr (Or.inr hη))
    simp [h0]

private theorem exists_streamPot {H : ℝ} (hH : 0 < H) {Ψ : Coord → Fin 2 → ℝ}
    (hΨ : IsPlanarSolTest Ψ)
    (hsupp : ∀ i : Fin 2, tsupport (fun x => Ψ x i) ⊆ Ioo 0 H ×ˢ univ) :
    ∃ (Φ : Coord → ℝ) (a b R : ℝ),
      0 < a ∧ a ≤ b ∧ b < H ∧ 0 < R ∧
      IsCoordTest Φ ∧
      tsupport Φ ⊆ Icc a b ×ˢ (Icc (-R) R ×ˢ Icc (-R) R) ∧
      (∀ x : Coord, Ψ x 0 = cpd 2 Φ x ∧ Ψ x 1 = -cpd 1 Φ x) := by
  obtain ⟨a, b, R, ha, hab, hbH, hR, hbox⟩ := planarSolTest_box hH hΨ hsupp
  let Φ : Coord → ℝ := streamPot R Ψ
  have hΦ_sm : ContDiff ℝ ∞ Φ := contDiff_streamPot R (hΨ.smooth 1).smooth
  let Box : Set Coord := Icc a b ×ˢ (Icc (-R) R ×ˢ Icc (-R) R)
  have hBox_comp : IsCompact Box := isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hsupp_sub : Function.support Φ ⊆ Box := by
    intro x hx
    by_contra hnot
    apply hx
    apply streamPot_eq_zero_outside hR hΨ hbox
    by_contra hgood
    push Not at hgood
    exact hnot ⟨hgood.1, abs_le.1 hgood.2.1, abs_le.1 hgood.2.2⟩
  have htsupp_sub : tsupport Φ ⊆ Box := closure_minimal hsupp_sub hBox_comp.isClosed
  have hΦ_test : IsCoordTest Φ :=
    ⟨hΦ_sm, hBox_comp.of_isClosed_subset (isClosed_tsupport Φ) htsupp_sub,
      fun x hx => ⟨lt_of_lt_of_le ha (htsupp_sub hx).1.1, trivial⟩⟩
  have hsupp0 : ∀ x : Coord, R < |x.2.1| → Ψ x 0 = 0 :=
    fun x hx => image_eq_zero_of_notMem_tsupport (f := fun z => Ψ z 0) (hbox 0 x (Or.inr (Or.inl hx)))
  refine ⟨Φ, a, b, R, ha, hab, hbH, hR, hΦ_test, htsupp_sub, fun x => ?_⟩
  exact ⟨(cpd2_streamPot hR hΨ hsupp0 x).symm, by rw [cpd1_streamPot R hΨ x, neg_neg]⟩

/-! ## 2. Joint smoothness, time derivative, and commutation of `qPeriodize` -/

private theorem notMem_box_vanish {a b R : ℝ} {α : Coord → ℝ}
    (hα : tsupport α ⊆ Icc a b ×ˢ (Icc (-R) R ×ˢ Icc (-R) R))
    (x : Coord) (hx : x.1 ∉ Icc a b ∨ R < |x.2.1| ∨ R < |x.2.2|) :
    α x = 0 := by
  apply image_eq_zero_of_notMem_tsupport
  intro hxt
  obtain ⟨hab, hq, hη⟩ := hα hxt
  rcases hx with h1 | h2 | h3
  · exact h1 hab
  · exact absurd (abs_le.2 hq) (not_le.2 h2)
  · exact absurd (abs_le.2 hη) (not_le.2 h3)

private theorem cpd_comm {g : Coord → ℝ} (hg : ContDiff ℝ ∞ g) (i j : Fin 3) :
    cpd i (cpd j g) = cpd j (cpd i g) := by
  funext x
  have hs : IsSymmSndFDerivAt ℝ g x := hg.contDiffAt.isSymmSndFDerivAt (by simp)
  have hA : cpd i (cpd j g) x = fderiv ℝ (fderiv ℝ g) x (cdir i) (cdir j) := by
    unfold cpd
    rw [(planarTest_hasFDerivAt_partial hg (cdir j) x).fderiv]
    rfl
  have hB : cpd j (cpd i g) x = fderiv ℝ (fderiv ℝ g) x (cdir j) (cdir i) := by
    unfold cpd
    rw [(planarTest_hasFDerivAt_partial hg (cdir i) x).fderiv]
    rfl
  rw [hA, hB]
  exact hs (cdir i) (cdir j)

private theorem qPeriodize_eq_finset_on_strip {c R Q : ℝ} (hc : 0 < c) {α : Coord → ℝ}
    (hα : ∀ x : Coord, R < |x.2.1| → α x = 0) :
    ∃ N : ℕ, ∀ (s : ℝ) (z : B0579.Plane), |z.1| ≤ Q →
      qPeriodize c α s z =
        ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), α (s, (z.1 + (k : ℝ) * c, z.2)) := by
  obtain ⟨N, hN⟩ := exists_nat_gt ((Q + R) / c + 1)
  refine ⟨N, fun s z hz => tsum_eq_sum fun k hk => ?_⟩
  apply hα
  dsimp
  rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hk
  have hk_abs : (N : ℝ) + 1 ≤ |(k : ℝ)| := by
    have hk_int : (N : ℤ) + 1 ≤ |k| := by
      rcases hk with hk | hk
      · rw [abs_of_neg (by omega)]; omega
      · rw [abs_of_nonneg (by omega)]; omega
    have hk_r : ((N : ℤ) + 1 : ℝ) ≤ (|k| : ℝ) := by exact_mod_cast hk_int
    simpa [Int.cast_abs] using hk_r
  have h1 : Q + R + c < ((N : ℝ) + 1) * c := by
    have hm := mul_lt_mul_of_pos_right hN hc
    have hdiv : ((Q + R) / c + 1) * c = Q + R + c := by field_simp [hc.ne']
    linarith
  have h2 : ((N : ℝ) + 1) * c ≤ |(k : ℝ)| * c := mul_le_mul_of_nonneg_right hk_abs hc.le
  have h3 : |(k : ℝ)| * c - |z.1| ≤ |z.1 + (k : ℝ) * c| := by
    have hsub := abs_sub_abs_le_abs_add ((k : ℝ) * c) z.1
    rw [add_comm, abs_mul, abs_of_pos hc] at hsub
    linarith
  linarith

private theorem continuous_qPeriodize_joint {c : ℝ} (hc : 0 < c) {α : Coord → ℝ}
    (hα : IsCoordTest α) :
    Continuous (fun p : ℝ × B0579.Plane => qPeriodize c α p.1 p.2) := by
  obtain ⟨_a, _b, R, _ha, _hab, _hR, hbox⟩ := coordTest_box hα
  have hq : ∀ x : Coord, R < |x.2.1| → α x = 0 := fun x hx => (hbox x (Or.inr (Or.inl hx))).1
  rw [continuous_iff_continuousAt]
  intro p₀
  obtain ⟨N, hN⟩ := qPeriodize_eq_finset_on_strip (Q := |p₀.2.1| + 1) hc hq
  have hU : {p : ℝ × B0579.Plane | |p.2.1| < |p₀.2.1| + 1} ∈ 𝓝 p₀ :=
    (isOpen_lt (continuous_fst.comp continuous_snd).abs continuous_const).mem_nhds
      (lt_add_one |p₀.2.1|)
  have hev : (fun p : ℝ × B0579.Plane => qPeriodize c α p.1 p.2) =ᶠ[𝓝 p₀]
      fun p : ℝ × B0579.Plane =>
        ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), α (p.1, (p.2.1 + (k : ℝ) * c, p.2.2)) :=
    Filter.eventually_of_mem hU fun p hp => hN p.1 p.2 (le_of_lt hp)
  refine ContinuousAt.congr ?_ hev.symm
  refine Continuous.continuousAt ?_
  refine continuous_finsetSum _ fun k _ => ?_
  exact hα.smooth.continuous.comp
    (continuous_fst.prodMk
      (((continuous_fst.comp continuous_snd).add continuous_const).prodMk
        (continuous_snd.comp continuous_snd)))

private theorem qPeriodize_eq_zero_of_s_notMem {c a b R : ℝ} {α : Coord → ℝ}
    (hα : tsupport α ⊆ Icc a b ×ˢ (Icc (-R) R ×ˢ Icc (-R) R))
    {s : ℝ} (hs : s ∉ Icc a b) :
    qPeriodize c α s = 0 := by
  funext z
  change qPeriodize c α s z = 0
  unfold qPeriodize
  have h0 : (fun k : ℤ => α (s, (z.1 + (k : ℝ) * c, z.2))) = fun _ => 0 :=
    funext fun k => notMem_box_vanish hα _ (Or.inl hs)
  rw [h0, tsum_zero]

private theorem qPeriodize_eq_zero_of_eta_gt {c a b R : ℝ} {α : Coord → ℝ}
    (hα : tsupport α ⊆ Icc a b ×ˢ (Icc (-R) R ×ˢ Icc (-R) R))
    (s : ℝ) {z : B0579.Plane} (hz : R < |z.2|) :
    qPeriodize c α s z = 0 := by
  unfold qPeriodize
  have h0 : (fun k : ℤ => α (s, (z.1 + (k : ℝ) * c, z.2))) = fun _ => 0 :=
    funext fun k => notMem_box_vanish hα _ (Or.inr (Or.inr hz))
  rw [h0, tsum_zero]

private theorem qPeriodize_uniform_bound {c H a b R : ℝ} (hc : 0 < c) {α : Coord → ℝ}
    (hα_test : IsCoordTest α)
    (hα_box : tsupport α ⊆ Icc a b ×ˢ (Icc (-R) R ×ˢ Icc (-R) R)) :
    ∃ B : ℝ, 0 < B ∧ ∀ s ∈ Icc 0 H, ∀ z : B0579.Plane, |z.1| ≤ c / 2 →
      |qPeriodize c α s z| ≤ B := by
  let K : Set (ℝ × B0579.Plane) := Icc 0 H ×ˢ (Icc (-(c / 2)) (c / 2) ×ˢ Icc (-R) R)
  have hK : IsCompact K := isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  obtain ⟨B₀, hB₀⟩ := hK.exists_bound_of_continuousOn
    (continuous_qPeriodize_joint hc hα_test).continuousOn
  refine ⟨max 1 B₀, lt_of_lt_of_le one_pos (le_max_left _ _), fun s hs z hz1 => ?_⟩
  by_cases hz2 : |z.2| ≤ R
  · have h := hB₀ (s, z) ⟨hs, abs_le.1 hz1, abs_le.1 hz2⟩
    rw [Real.norm_eq_abs] at h
    exact h.trans (le_max_right _ _)
  · rw [qPeriodize_eq_zero_of_eta_gt hα_box s (not_le.1 hz2), abs_zero]
    exact le_of_lt (lt_of_lt_of_le one_pos (le_max_left _ _))

private theorem qPeriodize_uniform_continuity {c H a b R : ℝ} (hc : 0 < c) {α : Coord → ℝ}
    (hα_test : IsCoordTest α)
    (hα_box : tsupport α ⊆ Icc a b ×ˢ (Icc (-R) R ×ˢ Icc (-R) R))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ r ∈ Icc 0 H, ∀ t ∈ Icc 0 H, |r - t| < δ →
      ∀ z : B0579.Plane, |z.1| ≤ c / 2 →
        |qPeriodize c α r z - qPeriodize c α t z| ≤ ε := by
  let K : Set (ℝ × B0579.Plane) := Icc 0 H ×ˢ (Icc (-(c / 2)) (c / 2) ×ˢ Icc (-R) R)
  have hK : IsCompact K := isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have huc : UniformContinuousOn (fun p : ℝ × B0579.Plane => qPeriodize c α p.1 p.2) K :=
    hK.uniformContinuousOn_of_continuous (continuous_qPeriodize_joint hc hα_test).continuousOn
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ, hδ, hmod⟩ := huc ε hε
  refine ⟨δ, hδ, fun r hr t ht hrt z hz1 => ?_⟩
  by_cases hz2 : |z.2| ≤ R
  · have hp1 : (r, z) ∈ K := ⟨hr, abs_le.1 hz1, abs_le.1 hz2⟩
    have hp2 : (t, z) ∈ K := ⟨ht, abs_le.1 hz1, abs_le.1 hz2⟩
    have hdist : dist (r, z) (t, z) < δ := by
      simpa [Prod.dist_eq, Real.dist_eq] using hrt
    exact le_of_lt (by simpa [Real.dist_eq] using hmod (r, z) hp1 (t, z) hp2 hdist)
  · have hz2' : R < |z.2| := not_le.1 hz2
    rw [qPeriodize_eq_zero_of_eta_gt hα_box r hz2',
      qPeriodize_eq_zero_of_eta_gt hα_box t hz2', sub_self, abs_zero]
    exact hε.le

private theorem tsupport_cpd_subset {α : Coord → ℝ} (j : Fin 3) :
    tsupport (cpd j α) ⊆ tsupport α := by
  refine closure_minimal (fun x hx => ?_) (isClosed_tsupport α)
  by_contra hnot
  exact hx (by simp [cpd, fderiv_of_notMem_tsupport (𝕜 := ℝ) hnot])

private theorem hasDerivAt_qPeriodize_time {c : ℝ} (hc : 0 < c) {α : Coord → ℝ}
    (hα : IsCoordTest α) (s : ℝ) (z : B0579.Plane) :
    HasDerivAt (fun t : ℝ => qPeriodize c α t z) (qPeriodize c (cpd 0 α) s z) s := by
  obtain ⟨_a, _b, R, _ha, _hab, _hR, hbox⟩ := coordTest_box hα
  have hq : ∀ x : Coord, R < |x.2.1| → α x = 0 := fun x hx => (hbox x (Or.inr (Or.inl hx))).1
  have hq0 : ∀ x : Coord, R < |x.2.1| → cpd 0 α x = 0 :=
    fun x hx => (hbox x (Or.inr (Or.inl hx))).2 0
  obtain ⟨M, hM⟩ := exists_nat_gt ((|z.1| + R) / c + 1)
  let T : Finset ℤ := Finset.Icc (-(M : ℤ)) (M : ℤ)
  have hout : ∀ (t : ℝ) {k : ℤ}, k ∉ T → R < |z.1 + (k : ℝ) * c| := by
    intro _ k hk
    rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hk
    have hk_abs : (M : ℝ) + 1 ≤ |(k : ℝ)| := by
      have hk_int : (M : ℤ) + 1 ≤ |k| := by
        rcases hk with hk | hk
        · rw [abs_of_neg (by omega)]; omega
        · rw [abs_of_nonneg (by omega)]; omega
      have hk_r : ((M : ℤ) + 1 : ℝ) ≤ (|k| : ℝ) := by exact_mod_cast hk_int
      simpa [Int.cast_abs] using hk_r
    have h1 : |z.1| + R + c < ((M : ℝ) + 1) * c := by
      have hm := mul_lt_mul_of_pos_right hM hc
      have hdiv : ((|z.1| + R) / c + 1) * c = |z.1| + R + c := by field_simp [hc.ne']
      linarith
    have h2 : ((M : ℝ) + 1) * c ≤ |(k : ℝ)| * c := mul_le_mul_of_nonneg_right hk_abs hc.le
    have h3 : |(k : ℝ)| * c - |z.1| ≤ |z.1 + (k : ℝ) * c| := by
      have hsub := abs_sub_abs_le_abs_add ((k : ℝ) * c) z.1
      rw [add_comm, abs_mul, abs_of_pos hc] at hsub
      linarith
    linarith
  have heq1 : (fun t : ℝ => qPeriodize c α t z) =
      fun t : ℝ => ∑ k ∈ T, α (t, (z.1 + (k : ℝ) * c, z.2)) :=
    funext fun t => tsum_eq_sum fun k hk => hq _ (hout t hk)
  have heq2 : qPeriodize c (cpd 0 α) s z =
      ∑ k ∈ T, cpd 0 α (s, (z.1 + (k : ℝ) * c, z.2)) :=
    tsum_eq_sum fun k hk => hq0 _ (hout s hk)
  rw [heq1, heq2]
  refine HasDerivAt.fun_sum fun k _ => ?_
  have h := hasDerivAt_coord_shift hα.smooth 0 (s, (z.1 + (k : ℝ) * c, z.2)) s
  exact h.congr_of_eventuallyEq (Eventually.of_forall fun t => by simp [cdir])

private theorem qPeriodize_sub_eq_setIntegral_Ioc {c : ℝ} (hc : 0 < c) {α : Coord → ℝ}
    (hα : IsCoordTest α) {t₁ t₂ : ℝ} (ht : t₁ ≤ t₂) (z : B0579.Plane) :
    qPeriodize c α t₂ z - qPeriodize c α t₁ z =
      ∫ r in Ioc t₁ t₂, qPeriodize c (cpd 0 α) r z := by
  have hα0 : IsCoordTest (cpd 0 α) := planarTest_isCoordTest_partial hα (cdir 0)
  have hcont : Continuous (fun r : ℝ => qPeriodize c (cpd 0 α) r z) :=
    (continuous_qPeriodize_joint hc hα0).comp (continuous_id.prodMk continuous_const)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun r _ => hasDerivAt_qPeriodize_time hc hα r z) (hcont.intervalIntegrable t₁ t₂)
  rw [intervalIntegral.integral_of_le ht] at hftc
  exact hftc.symm

/-! ## 3. Uniform `Xmc` bounds, continuity in `r`, and time-stepping on `[0, H]` -/

private theorem source_strip_bound {c m R B : ℝ} (hm : 1 / 2 < m) (hB : 0 < B)
    {C1 : ℝ} (hC1nn : 0 ≤ C1)
    (hC1 : ∀ w : Xmc c m, eLpNorm (⇑w) 1 (volume.restrict (B0579.cell c)) ≤
      ENNReal.ofReal C1 * ‖w‖ₑ)
    {ψ : B0579.Plane → ℝ} (hψ_meas : Measurable ψ)
    (hψ_bd : ∀ x : B0579.Plane, |x.1| ≤ c / 2 → |ψ x| ≤ B)
    (_hψ_van : ∀ x : B0579.Plane, R < |x.2| → ψ x = 0)
    (w : Xmc c m) :
    IntegrableOn (fun x => w x * ψ x) (B0579.cell c) volume ∧
      ‖∫ x in B0579.cell c, w x * ψ x‖ ≤ C1 * B * ‖w‖ := by
  have hwm : AEStronglyMeasurable (⇑w) (volume.restrict (B0579.cell c)) :=
    (Lp.aestronglyMeasurable w).mono_ac (B0579.ac_cellMeasure c m)
  have hfm : AEStronglyMeasurable (fun x => w x * ψ x) (volume.restrict (B0579.cell c)) :=
    hwm.mul hψ_meas.aestronglyMeasurable
  have hlin : ∫⁻ x in B0579.cell c, ‖w x * ψ x‖ₑ ≤ ENNReal.ofReal (B * C1) * ‖w‖ₑ := by
    calc ∫⁻ x in B0579.cell c, ‖w x * ψ x‖ₑ
        ≤ ∫⁻ x in B0579.cell c, ENNReal.ofReal B * ‖w x‖ₑ := by
          refine setLIntegral_mono' (B0579.measurableSet_cell c) fun x hx => ?_
          have hx1 : |x.1| ≤ c / 2 := abs_le.2 ⟨hx.1.1, hx.1.2.le⟩
          rw [enorm_mul, mul_comm]
          gcongr
          rw [← ofReal_norm]
          exact ENNReal.ofReal_le_ofReal (by simpa using hψ_bd x hx1)
      _ = ENNReal.ofReal B * eLpNorm (⇑w) 1 (volume.restrict (B0579.cell c)) := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, eLpNorm_one_eq_lintegral_enorm]
      _ ≤ ENNReal.ofReal B * (ENNReal.ofReal C1 * ‖w‖ₑ) := by gcongr; exact hC1 w
      _ = ENNReal.ofReal (B * C1) * ‖w‖ₑ := by
          rw [ENNReal.ofReal_mul hB.le, mul_assoc]
  have hint : IntegrableOn (fun x => w x * ψ x) (B0579.cell c) volume :=
    ⟨hfm, lt_of_le_of_lt hlin (ENNReal.mul_lt_top ENNReal.ofReal_lt_top enorm_lt_top)⟩
  refine ⟨hint, ?_⟩
  have h1 : ‖∫ x in B0579.cell c, w x * ψ x‖ ≤ ∫ x in B0579.cell c, ‖w x * ψ x‖ :=
    norm_integral_le_integral_norm _
  have h2 : ∫ x in B0579.cell c, ‖w x * ψ x‖ = (∫⁻ x in B0579.cell c, ‖w x * ψ x‖ₑ).toReal :=
    integral_norm_eq_lintegral_enorm hfm
  have h3 : (∫⁻ x in B0579.cell c, ‖w x * ψ x‖ₑ).toReal ≤
      (ENNReal.ofReal (B * C1) * ‖w‖ₑ).toReal :=
    ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top enorm_ne_top) hlin
  have h4 : (ENNReal.ofReal (B * C1) * ‖w‖ₑ).toReal = C1 * B * ‖w‖ := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (mul_nonneg hB.le hC1nn)]
    change (B * C1) * ‖w‖ = C1 * B * ‖w‖
    ring
  have _ := hm
  linarith

private theorem sourcePairCLM {c m : ℝ} (hm : 1 / 2 < m) {ψ : B0579.Plane → ℝ}
    (hψ : B0579.IsCylTest c ψ) :
    ∃ T : Xmc c m →L[ℝ] ℝ, ∀ w : Xmc c m,
      IntegrableOn (fun x => w x * ψ x) (B0579.cell c) volume ∧
        T w = ∫ x in B0579.cell c, w x * ψ x := by
  obtain ⟨R, B₀, hR, hB₀, hRB⟩ := CCP.test_single hψ
  obtain ⟨C1, hC1nn, hC1⟩ := CCP.exists_L1_const c m hm
  let B : ℝ := B₀ + 1
  have hB : 0 < B := by linarith
  have hbd : ∀ w : Xmc c m,
      ∫⁻ x in B0579.cell c, ‖w x * ψ x‖ₑ ≤ ENNReal.ofReal (C1 * B) * ‖w‖ₑ := by
    intro w
    calc ∫⁻ x in B0579.cell c, ‖w x * ψ x‖ₑ
        ≤ ∫⁻ x in B0579.cell c, ENNReal.ofReal B * ‖w x‖ₑ := by
          refine setLIntegral_mono' (B0579.measurableSet_cell c) fun x hx => ?_
          have hx1 : |x.1| ≤ c / 2 := abs_le.2 ⟨hx.1.1, hx.1.2.le⟩
          have hxB : |ψ x| ≤ B := ((hRB x).1 hx1).trans (by linarith)
          rw [enorm_mul, mul_comm]
          gcongr
          rw [← ofReal_norm]
          exact ENNReal.ofReal_le_ofReal (by simpa using hxB)
      _ = ENNReal.ofReal B * eLpNorm (⇑w) 1 (volume.restrict (B0579.cell c)) := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, eLpNorm_one_eq_lintegral_enorm]
      _ ≤ ENNReal.ofReal B * (ENNReal.ofReal C1 * ‖w‖ₑ) := by gcongr; exact hC1 w
      _ = ENNReal.ofReal (C1 * B) * ‖w‖ₑ := by
          rw [ENNReal.ofReal_mul hC1nn]; ring
  obtain ⟨T, _, hT⟩ := CCP.clm_of_bound (c := c) (m := m)
    (fun w x => w x * ψ x) (C1 * B) (mul_nonneg hC1nn hB.le)
    (fun w => ((Lp.aestronglyMeasurable w).mono_ac (B0579.ac_cellMeasure c m)).mul
      hψ.continuous.measurable.aestronglyMeasurable)
    hbd
    (fun w1 w2 => by
      filter_upwards [CCP.coe_add_ae w1 w2] with x hx
      rw [hx]; ring)
    (fun a w => by
      filter_upwards [CCP.coe_smul_ae a w] with x hx
      rw [hx]; ring)
  have _ := hR
  exact ⟨T, hT⟩

private theorem coupled_strip_bound_exists {ν c m H R : ℝ} (hc1 : 1 ≤ c) (hm : 1 / 2 < m)
    (hH : 0 ≤ H) (hR : 0 ≤ R) (tr : B0140.TrainSol ν c) :
    ∃ C_op : ℝ, 0 ≤ C_op ∧
      ∀ {B : ℝ}, 0 < B → ∀ {ψ : B0579.Plane → ℝ}, B0579.IsCylTest c ψ →
        (∀ x : B0579.Plane, |x.1| ≤ c / 2 →
          |ψ x| ≤ B ∧ |B0579.pd 0 ψ x| ≤ B ∧ |B0579.pd 1 ψ x| ≤ B ∧
            |B0579.pd 0 (B0579.pd 0 ψ) x + B0579.pd 1 (B0579.pd 1 ψ) x| ≤ 2 * B) →
        (∀ x : B0579.Plane, R < |x.2| →
          ψ x = 0 ∧ B0579.pd 0 ψ x = 0 ∧ B0579.pd 1 ψ x = 0 ∧
            B0579.pd 0 (B0579.pd 0 ψ) x + B0579.pd 1 (B0579.pd 1 ψ) x = 0) →
        ∀ r ∈ Icc 0 H, ∀ w : Xmc c m,
          IntegrableOn (cylCoupledIntegrand tr (⇑w) r ψ) (B0579.cell c) volume ∧
            ‖∫ x in B0579.cell c, cylCoupledIntegrand tr (⇑w) r ψ x‖ ≤ C_op * B * ‖w‖ := by
  obtain ⟨Ctr, hCtr, hCtr_bd⟩ := CCP.train_strip_bounds tr H R hH
  obtain ⟨C1, hC1, hC1w⟩ := CCP.exists_L1_const c m hm
  obtain ⟨CK1, hCK1, hKb1⟩ := CCP.K_pair_bound hc1 hm R (Ctr + 1) hR
  let A₀ : ℝ := |ν| * 2 + 2 * Ctr
  have hA₀ : 0 ≤ A₀ := by positivity
  let C_op : ℝ := A₀ * C1 + 2 * CK1
  refine ⟨C_op, by positivity, fun {B} hB {ψ} hψ hψ_bd hψ_van r hr w => ?_⟩
  obtain ⟨_M, hMb⟩ := CCP.main_bound hc1 hm tr H hH hψ
  have hmeas : AEStronglyMeasurable (cylCoupledIntegrand tr (⇑w) r ψ)
      (volume.restrict (B0579.cell c)) := (hMb.2 r hr w).1
  have hint : IntegrableOn (cylCoupledIntegrand tr (⇑w) r ψ) (B0579.cell c) volume :=
    ⟨hmeas, lt_of_le_of_lt (hMb.2 r hr w).2 (ENNReal.mul_lt_top ENNReal.ofReal_lt_top enorm_lt_top)⟩
  set a : B0579.Plane → ℝ := fun x =>
    ν * (B0579.pd 0 (B0579.pd 0 ψ) x + B0579.pd 1 (B0579.pd 1 ψ) x) +
      (tr.v r x 0 * B0579.pd 0 ψ x + tr.v r x 1 * B0579.pd 1 ψ x)
  set ψ0 : B0579.Plane → ℝ := fun x => ψ x * B0579.pd 0 (B0238.Ec tr r) x
  set ψ1 : B0579.Plane → ℝ := fun x => ψ x * B0579.pd 1 (B0238.Ec tr r) x
  have hab : ∀ x ∈ B0579.cell c, |a x| ≤ A₀ * B := by
    intro x hx
    have hx1 : |x.1| ≤ c / 2 := abs_le.2 ⟨hx.1.1, hx.1.2.le⟩
    by_cases hx2 : |x.2| ≤ R
    · obtain ⟨_, hp0, hp1, hlap⟩ := hψ_bd x hx1
      obtain ⟨hv0, hv1, _, _⟩ := hCtr_bd r hr x hx1 hx2
      calc |a x| ≤ |ν| * |B0579.pd 0 (B0579.pd 0 ψ) x + B0579.pd 1 (B0579.pd 1 ψ) x| +
            (|tr.v r x 0| * |B0579.pd 0 ψ x| + |tr.v r x 1| * |B0579.pd 1 ψ x|) := by
            dsimp [a]
            refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
            · rw [abs_mul]
            · refine (abs_add_le _ _).trans ?_
              rw [abs_mul, abs_mul]
        _ ≤ |ν| * (2 * B) + (Ctr * B + Ctr * B) := by gcongr
        _ = A₀ * B := by dsimp [A₀]; ring
    · obtain ⟨_, hp0, hp1, hlap⟩ := hψ_van x (not_le.1 hx2)
      dsimp [a]
      rw [hlap, hp0, hp1]
      simp; positivity
  have e1 : ∫⁻ x in B0579.cell c, ‖w x * a x‖ₑ ≤ ENNReal.ofReal (A₀ * C1 * B) * ‖w‖ₑ := by
    calc ∫⁻ x in B0579.cell c, ‖w x * a x‖ₑ
        ≤ ∫⁻ x in B0579.cell c, ENNReal.ofReal (A₀ * B) * ‖w x‖ₑ := by
          refine setLIntegral_mono' (B0579.measurableSet_cell c) fun x hx => ?_
          rw [enorm_mul, mul_comm]; gcongr
          rw [← ofReal_norm]
          exact ENNReal.ofReal_le_ofReal (by simpa using hab x hx)
      _ = ENNReal.ofReal (A₀ * B) * eLpNorm (⇑w) 1 (volume.restrict (B0579.cell c)) := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, eLpNorm_one_eq_lintegral_enorm]
      _ ≤ ENNReal.ofReal (A₀ * B) * (ENNReal.ofReal C1 * ‖w‖ₑ) := by gcongr; exact hC1w w
      _ = ENNReal.ofReal (A₀ * C1 * B) * ‖w‖ₑ := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (mul_nonneg hA₀ hB.le)]
          congr 2; ring
  have hK_scaled : ∀ (j : Fin 2) (χ : B0579.Plane → ℝ),
      (χ = fun x => ψ x * B0579.pd j (B0238.Ec tr r) x) →
      ∫⁻ x in B0579.cell c, ‖Cyl.K c (⇑w) x j * χ x‖ₑ ≤ ENNReal.ofReal (CK1 * B) * ‖w‖ₑ := by
    intro j χ hχ
    subst hχ
    let χ' : B0579.Plane → ℝ := fun x => B⁻¹ * (ψ x * B0579.pd j (B0238.Ec tr r) x)
    have hχ'1 : ∀ x : B0579.Plane, |x.1| ≤ c / 2 → |χ' x| ≤ Ctr + 1 := by
      intro x hx1
      by_cases hx2 : |x.2| ≤ R
      · have h0 := (hψ_bd x hx1).1
        have h3 := hCtr_bd r hr x hx1 hx2
        have h4 : |B0579.pd j (B0238.Ec tr r) x| ≤ Ctr := by
          fin_cases j
          · exact h3.2.2.1
          · exact h3.2.2.2
        dsimp [χ']
        rw [abs_mul, abs_mul, abs_inv, abs_of_pos hB]
        have hle1 : B⁻¹ * |ψ x| ≤ 1 := by
          rw [inv_mul_le_iff₀ hB]; linarith
        calc B⁻¹ * (|ψ x| * |B0579.pd j (B0238.Ec tr r) x|)
            = (B⁻¹ * |ψ x|) * |B0579.pd j (B0238.Ec tr r) x| := by ring
          _ ≤ 1 * Ctr := mul_le_mul hle1 h4 (abs_nonneg _) zero_le_one
          _ ≤ Ctr + 1 := by linarith
      · have h0 := (hψ_van x (not_le.1 hx2)).1
        dsimp [χ']; rw [h0]; simp; positivity
    have hχ'2 : ∀ x : B0579.Plane, R < |x.2| → χ' x = 0 := by
      intro x hx2
      dsimp [χ']; rw [(hψ_van x hx2).1]; simp
    have hb := hKb1 χ' hχ'1 hχ'2 w j
    have hpt : ∀ x, ‖Cyl.K c (⇑w) x j * (ψ x * B0579.pd j (B0238.Ec tr r) x)‖ₑ =
        ENNReal.ofReal B * ‖Cyl.K c (⇑w) x j * χ' x‖ₑ := by
      intro x
      have heq : Cyl.K c (⇑w) x j * (ψ x * B0579.pd j (B0238.Ec tr r) x) =
          B * (Cyl.K c (⇑w) x j * χ' x) := by
        dsimp [χ']; field_simp [hB.ne']
      rw [heq, enorm_mul, ← ofReal_norm B, Real.norm_of_nonneg hB.le]
    simp_rw [hpt]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    calc ENNReal.ofReal B * ∫⁻ x in B0579.cell c, ‖Cyl.K c (⇑w) x j * χ' x‖ₑ
        ≤ ENNReal.ofReal B * (ENNReal.ofReal CK1 * ‖w‖ₑ) := by gcongr
      _ = ENNReal.ofReal (CK1 * B) * ‖w‖ₑ := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul hB.le, mul_comm B CK1]
  have e2 := hK_scaled 0 ψ0 rfl
  have e3 := hK_scaled 1 ψ1 rfl
  have hwm : AEStronglyMeasurable (⇑w) (volume.restrict (B0579.cell c)) :=
    (Lp.aestronglyMeasurable w).mono_ac (B0579.ac_cellMeasure c m)
  have ham : Measurable a := by
    have p0 := CCP.pd_meas ψ 0
    have p1 := CCP.pd_meas ψ 1
    have h00 := CCP.pd_meas (B0579.pd 0 ψ) 0
    have h11 := CCP.pd_meas (B0579.pd 1 ψ) 1
    have hv0 := CCP.continuous_train_slice tr hr.1 0
    have hv1 := CCP.continuous_train_slice tr hr.1 1
    exact ((h00.add h11).const_mul ν).add ((hv0.measurable.mul p0).add (hv1.measurable.mul p1))
  have t1m : AEStronglyMeasurable (fun x => w x * a x) (volume.restrict (B0579.cell c)) :=
    hwm.mul ham.aestronglyMeasurable
  have t2m : AEStronglyMeasurable (fun x => Cyl.K c (⇑w) x 0 * ψ0 x)
      (volume.restrict (B0579.cell c)) :=
    ((CCP.K_comp_aesm hm w 0).restrict).mul
      (hψ.continuous.measurable.mul (CCP.measurable_pd_Ec tr r 0)).aestronglyMeasurable
  have hlin : ∫⁻ x in B0579.cell c, ‖cylCoupledIntegrand tr (⇑w) r ψ x‖ₑ ≤
      ENNReal.ofReal (C_op * B) * ‖w‖ₑ := by
    calc ∫⁻ x in B0579.cell c, ‖cylCoupledIntegrand tr (⇑w) r ψ x‖ₑ
        ≤ ∫⁻ x in B0579.cell c,
            ((‖w x * a x‖ₑ + ‖Cyl.K c (⇑w) x 0 * ψ0 x‖ₑ) + ‖Cyl.K c (⇑w) x 1 * ψ1 x‖ₑ) := by
          refine lintegral_mono fun x => ?_
          rw [CCP.integrand_eq]
          exact enorm_sub_le.trans (add_le_add enorm_sub_le le_rfl)
      _ = (∫⁻ x in B0579.cell c, ‖w x * a x‖ₑ) +
            (∫⁻ x in B0579.cell c, ‖Cyl.K c (⇑w) x 0 * ψ0 x‖ₑ) +
            (∫⁻ x in B0579.cell c, ‖Cyl.K c (⇑w) x 1 * ψ1 x‖ₑ) := by
          have t12m : AEMeasurable
              (fun x => ‖w x * a x‖ₑ + ‖Cyl.K c (⇑w) x 0 * ψ0 x‖ₑ)
              (volume.restrict (B0579.cell c)) := t1m.enorm.add t2m.enorm
          rw [lintegral_add_left' t12m, lintegral_add_left' t1m.enorm]
      _ ≤ ENNReal.ofReal (A₀ * C1 * B) * ‖w‖ₑ + ENNReal.ofReal (CK1 * B) * ‖w‖ₑ +
            ENNReal.ofReal (CK1 * B) * ‖w‖ₑ := by gcongr
      _ = ENNReal.ofReal (C_op * B) * ‖w‖ₑ := by
          have h1 : 0 ≤ A₀ * C1 * B := by positivity
          have h2 : 0 ≤ CK1 * B := by positivity
          rw [← add_mul, ← add_mul, ← ENNReal.ofReal_add h1 h2,
            ← ENNReal.ofReal_add (add_nonneg h1 h2) h2]
          congr 2
          dsimp [C_op]; ring
  refine ⟨hint, ?_⟩
  have n1 : ‖∫ x in B0579.cell c, cylCoupledIntegrand tr (⇑w) r ψ x‖ ≤
      ∫ x in B0579.cell c, ‖cylCoupledIntegrand tr (⇑w) r ψ x‖ :=
    norm_integral_le_integral_norm _
  have n2 : ∫ x in B0579.cell c, ‖cylCoupledIntegrand tr (⇑w) r ψ x‖ =
      (∫⁻ x in B0579.cell c, ‖cylCoupledIntegrand tr (⇑w) r ψ x‖ₑ).toReal :=
    integral_norm_eq_lintegral_enorm hmeas
  have n3 : (∫⁻ x in B0579.cell c, ‖cylCoupledIntegrand tr (⇑w) r ψ x‖ₑ).toReal ≤
      (ENNReal.ofReal (C_op * B) * ‖w‖ₑ).toReal :=
    ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top enorm_ne_top) hlin
  have n4 : (ENNReal.ofReal (C_op * B) * ‖w‖ₑ).toReal = C_op * B * ‖w‖ := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
    rfl
  linarith

private theorem continuousOn_pd_Ec_joint {ν c H : ℝ} (hH : 0 ≤ H) (tr : B0140.TrainSol ν c) :
    ∀ j : Fin 2, ContinuousOn
      (fun y : ℝ × B0579.Plane => B0579.pd j (B0238.Ec tr y.1) y.2)
      (Icc 0 H ×ˢ univ) := by
  set T : ℝ := H + 1
  have hT0 : 0 < T := by linarith
  set S : Set (ℝ × Cyl.Plane) := Icc 0 T ×ˢ (univ : Set Cyl.Plane)
  have huniq : UniqueDiffOn ℝ S := UniqueDiffOn.prod (uniqueDiffOn_Icc hT0) uniqueDiffOn_univ
  have hsm : ContDiffOn ℝ ∞ (fun x : ℝ × Cyl.Plane => tr.v x.1 x.2) S :=
    tr.isTrain.smooth_v.mono (prod_mono Icc_subset_Ici_self Subset.rfl)
  have hF1 := UnforcedLeray.Short.PartI.crFc_contDiffOn hsm 1
  have hF0 := UnforcedLeray.Short.PartI.crFc_contDiffOn hsm 0
  set E' : ℝ × Cyl.Plane → ℝ := fun x =>
    fderivWithin ℝ (UnforcedLeray.Short.PartI.crFc tr.v 1) S x UnforcedLeray.Short.PartI.crEQ -
      fderivWithin ℝ (UnforcedLeray.Short.PartI.crFc tr.v 0) S x UnforcedLeray.Short.PartI.crEE
  have hE'sm : ContDiffOn ℝ ∞ E' S :=
    ((hF1.fderivWithin huniq (by simp)).clm_apply contDiffOn_const).sub
      ((hF0.fderivWithin huniq (by simp)).clm_apply contDiffOn_const)
  have hcurl : ∀ r ∈ Icc (0 : ℝ) T, B0238.Ec tr r = fun z => E' (r, z) :=
    fun r hr => funext fun z => UnforcedLeray.Short.PartI.crCurl_within hsm hr
  intro j
  have hcontS : ContinuousOn (fun y => fderivWithin ℝ E' S y (0, B0579.dir j)) S :=
    (hE'sm.continuousOn_fderivWithin huniq (by simp)).clm_apply continuousOn_const
  have hsub : Icc 0 H ×ˢ (univ : Set B0579.Plane) ⊆ S :=
    fun y hy => ⟨⟨hy.1.1, hy.1.2.trans (by linarith)⟩, trivial⟩
  refine (hcontS.mono hsub).congr ?_
  intro ⟨r, z⟩ hrz
  have hrT : r ∈ Icc (0 : ℝ) T := ⟨hrz.1.1, hrz.1.2.trans (by linarith)⟩
  have hd : HasFDerivWithinAt E' (fderivWithin ℝ E' S (r, z)) S (r, z) :=
    ((hE'sm.differentiableOn (by simp)) _ ⟨hrT, trivial⟩).hasFDerivWithinAt
  have hι : HasFDerivAt (fun y : Cyl.Plane => ((r, y) : ℝ × Cyl.Plane))
      ((0 : Cyl.Plane →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ Cyl.Plane)) z :=
    (hasFDerivAt_const r z).prodMk (hasFDerivAt_id z)
  have hcomp := hd.comp z (hι.hasFDerivWithinAt (s := Set.univ)) (fun _ _ => ⟨hrT, trivial⟩)
  have hfd : HasFDerivAt (fun y : Cyl.Plane => E' (r, y))
      ((fderivWithin ℝ E' S (r, z)).comp
        ((0 : Cyl.Plane →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ Cyl.Plane))) z :=
    hasFDerivWithinAt_univ.mp hcomp
  unfold B0579.pd
  dsimp
  rw [hcurl r hrT, hfd.fderiv]
  simp

private theorem continuousOn_coupled_fixed_test {ν c m H : ℝ} (hc1 : 1 ≤ c) (hm : 1 / 2 < m)
    (hH : 0 ≤ H) (tr : B0140.TrainSol ν c) {om : ℝ → Xmc c m}
    (hom : ContinuousOn om (Icc 0 H)) {ψ : B0579.Plane → ℝ} (hψ : B0579.IsCylTest c ψ) :
    ContinuousOn (fun r => ∫ x in B0579.cell c, cylCoupledIntegrand tr (om r) r ψ x) (Icc 0 H) := by
  -- First prove continuity in r for a fixed w₀ ∈ Xmc c m via DCT
  have hfixed : ∀ w₀ : Xmc c m,
      ContinuousOn (fun r => ∫ x in B0579.cell c, cylCoupledIntegrand tr (⇑w₀) r ψ x) (Icc 0 H) := by
    intro w₀ r₀ hr₀
    rw [ContinuousWithinAt]
    obtain ⟨R, B, hR, hB, hRB⟩ := CCP.test_bounds hψ
    obtain ⟨Ctr, hCtr, hCtr_bd⟩ := CCP.train_strip_bounds tr H R hH
    obtain ⟨_C1, _hC1, hC1w⟩ := CCP.exists_L1_const c m hm
    set A : ℝ := |ν| * (2 * B) + (Ctr * B + Ctr * B)
    set T0 : Set B0579.Plane := Icc (-(c / 2)) (c / 2) ×ˢ Icc (-R) R
    have hT0m : MeasurableSet T0 := (isClosed_Icc.prod isClosed_Icc).measurableSet
    set W : B0579.Plane → ℝ := T0.indicator (fun _ => (1 : ℝ))
    have hWm : Measurable W := measurable_const.indicator hT0m
    obtain ⟨_CK, _hCK, hKb⟩ := CCP.K_pair_bound hc1 hm R (B * Ctr) hR
    have hWI_1 : ∀ x, |x.1| ≤ c / 2 → |B * Ctr * W x| ≤ B * Ctr := by
      intro x _
      rw [abs_mul, abs_of_nonneg (mul_nonneg hB hCtr)]
      have hW1 : |W x| ≤ 1 := by
        dsimp [W]
        by_cases hxT : x ∈ T0 <;> simp [hxT]
      exact mul_le_of_le_one_right (mul_nonneg hB hCtr) hW1
    have hWI_2 : ∀ x, R < |x.2| → B * Ctr * W x = 0 := by
      intro x hx2
      have hxT : x ∉ T0 := fun h => absurd (abs_le.2 h.2) (not_le.2 hx2)
      simp [W, hxT]
    have hK0_int : IntegrableOn (fun x => ‖Cyl.K c (⇑w₀) x 0 * (B * Ctr * W x)‖)
        (B0579.cell c) volume := by
      refine ⟨(((CCP.K_comp_aesm hm w₀ 0).restrict).mul
        (hWm.const_mul (B * Ctr)).aestronglyMeasurable).norm, ?_⟩
      rw [hasFiniteIntegral_iff_enorm]
      simp_rw [enorm_norm]
      exact lt_of_le_of_lt (hKb _ hWI_1 hWI_2 w₀ 0)
        (ENNReal.mul_lt_top ENNReal.ofReal_lt_top enorm_lt_top)
    have hK1_int : IntegrableOn (fun x => ‖Cyl.K c (⇑w₀) x 1 * (B * Ctr * W x)‖)
        (B0579.cell c) volume := by
      refine ⟨(((CCP.K_comp_aesm hm w₀ 1).restrict).mul
        (hWm.const_mul (B * Ctr)).aestronglyMeasurable).norm, ?_⟩
      rw [hasFiniteIntegral_iff_enorm]
      simp_rw [enorm_norm]
      exact lt_of_le_of_lt (hKb _ hWI_1 hWI_2 w₀ 1)
        (ENNReal.mul_lt_top ENNReal.ofReal_lt_top enorm_lt_top)
    have hw_int : IntegrableOn (fun x => A * ‖w₀ x‖) (B0579.cell c) volume := by
      have h1 : IntegrableOn (fun x => ‖w₀ x‖) (B0579.cell c) volume := by
        refine ⟨((Lp.aestronglyMeasurable w₀).mono_ac (B0579.ac_cellMeasure c m)).norm, ?_⟩
        rw [hasFiniteIntegral_iff_enorm]
        simp_rw [enorm_norm, ← eLpNorm_one_eq_lintegral_enorm]
        exact lt_of_le_of_lt (hC1w w₀) (ENNReal.mul_lt_top ENNReal.ofReal_lt_top enorm_lt_top)
      exact h1.const_mul A
    let bound : B0579.Plane → ℝ := fun x =>
      A * ‖w₀ x‖ + ‖Cyl.K c (⇑w₀) x 0 * (B * Ctr * W x)‖ + ‖Cyl.K c (⇑w₀) x 1 * (B * Ctr * W x)‖
    have hbound_int : Integrable bound (volume.restrict (B0579.cell c)) :=
      (hw_int.add hK0_int).add hK1_int
    obtain ⟨_M, hMb⟩ := CCP.main_bound hc1 hm tr H hH hψ
    have hcont_Ec := continuousOn_pd_Ec_joint hH tr
    have hcont_v : ∀ i : Fin 2, ContinuousOn (fun y : ℝ × B0579.Plane => tr.v y.1 y.2 i)
        (Icc 0 H ×ˢ univ) := fun i =>
      (EuclideanSpace.proj (𝕜 := ℝ) i).continuous.comp_continuousOn
        (tr.isTrain.smooth_v.continuousOn.mono (prod_mono Icc_subset_Ici_self Subset.rfl))
    refine tendsto_integral_filter_of_dominated_convergence bound ?_ ?_ hbound_int ?_
    · filter_upwards [self_mem_nhdsWithin] with r hr
      exact (hMb.2 r hr w₀).1
    · filter_upwards [self_mem_nhdsWithin] with r hr
      refine (ae_restrict_iff' (B0579.measurableSet_cell c)).2 (Eventually.of_forall fun x hx => ?_)
      have hx1 : |x.1| ≤ c / 2 := abs_le.2 ⟨hx.1.1, hx.1.2.le⟩
      rw [CCP.integrand_eq]
      by_cases hx2 : |x.2| ≤ R
      · have hxT : x ∈ T0 := ⟨abs_le.1 hx1, abs_le.1 hx2⟩
        have hWx : W x = 1 := Set.indicator_of_mem hxT _
        have h1 := (hRB x).1 hx1
        have h3 := hCtr_bd r hr x hx1 hx2
        have ha_le : |ν * (B0579.pd 0 (B0579.pd 0 ψ) x + B0579.pd 1 (B0579.pd 1 ψ) x) +
            (tr.v r x 0 * B0579.pd 0 ψ x + tr.v r x 1 * B0579.pd 1 ψ x)| ≤ A := by
          refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
          · rw [abs_mul]; gcongr; exact h1.2.2.2
          · refine (abs_add_le _ _).trans ?_
            rw [abs_mul, abs_mul]; gcongr
            · exact h3.1
            · exact h1.2.1
            · exact h3.2.1
            · exact h1.2.2.1
        have h0_le : |ψ x * B0579.pd 0 (B0238.Ec tr r) x| ≤ B * Ctr := by
          rw [abs_mul]; exact mul_le_mul h1.1 h3.2.2.1 (abs_nonneg _) hB
        have h1_le : |ψ x * B0579.pd 1 (B0238.Ec tr r) x| ≤ B * Ctr := by
          rw [abs_mul]; exact mul_le_mul h1.1 h3.2.2.2 (abs_nonneg _) hB
        simp only [bound, hWx, mul_one, Real.norm_eq_abs]
        calc |w₀ x * (ν * (B0579.pd 0 (B0579.pd 0 ψ) x + B0579.pd 1 (B0579.pd 1 ψ) x) +
                (tr.v r x 0 * B0579.pd 0 ψ x + tr.v r x 1 * B0579.pd 1 ψ x)) -
              Cyl.K c (⇑w₀) x 0 * (ψ x * B0579.pd 0 (B0238.Ec tr r) x) -
              Cyl.K c (⇑w₀) x 1 * (ψ x * B0579.pd 1 (B0238.Ec tr r) x)|
            ≤ |w₀ x| * |ν * (B0579.pd 0 (B0579.pd 0 ψ) x + B0579.pd 1 (B0579.pd 1 ψ) x) +
                (tr.v r x 0 * B0579.pd 0 ψ x + tr.v r x 1 * B0579.pd 1 ψ x)| +
              |Cyl.K c (⇑w₀) x 0| * |ψ x * B0579.pd 0 (B0238.Ec tr r) x| +
              |Cyl.K c (⇑w₀) x 1| * |ψ x * B0579.pd 1 (B0238.Ec tr r) x| := by
                have s1 := abs_sub (w₀ x * (ν * (B0579.pd 0 (B0579.pd 0 ψ) x + B0579.pd 1 (B0579.pd 1 ψ) x) +
                  (tr.v r x 0 * B0579.pd 0 ψ x + tr.v r x 1 * B0579.pd 1 ψ x)) -
                  Cyl.K c (⇑w₀) x 0 * (ψ x * B0579.pd 0 (B0238.Ec tr r) x))
                  (Cyl.K c (⇑w₀) x 1 * (ψ x * B0579.pd 1 (B0238.Ec tr r) x))
                have s2 := abs_sub (w₀ x * (ν * (B0579.pd 0 (B0579.pd 0 ψ) x + B0579.pd 1 (B0579.pd 1 ψ) x) +
                  (tr.v r x 0 * B0579.pd 0 ψ x + tr.v r x 1 * B0579.pd 1 ψ x)))
                  (Cyl.K c (⇑w₀) x 0 * (ψ x * B0579.pd 0 (B0238.Ec tr r) x))
                rw [abs_mul] at s1
                rw [abs_mul, abs_mul] at s2
                linarith
          _ ≤ |w₀ x| * A + |Cyl.K c (⇑w₀) x 0| * (B * Ctr) + |Cyl.K c (⇑w₀) x 1| * (B * Ctr) := by
                gcongr
          _ = A * |w₀ x| + |Cyl.K c (⇑w₀) x 0 * (B * Ctr)| + |Cyl.K c (⇑w₀) x 1 * (B * Ctr)| := by
                simp only [abs_mul, abs_of_nonneg hB, abs_of_nonneg hCtr]
                ring
      · have h5 := (hRB x).2 (not_le.1 hx2)
        rw [h5.1, h5.2.1, h5.2.2.1, h5.2.2.2]
        simp only [mul_zero, zero_mul, add_zero, sub_self, norm_zero]
        dsimp [bound]
        positivity
    · refine Eventually.of_forall fun x => ?_
      have hmap : Tendsto (fun r : ℝ => (r, x)) (𝓝[Icc 0 H] r₀)
          (𝓝[Icc 0 H ×ˢ univ] (r₀, x)) :=
        tendsto_nhdsWithin_iff.2
          ⟨((continuous_id.prodMk continuous_const).tendsto r₀).mono_left nhdsWithin_le_nhds,
            Filter.eventually_of_mem self_mem_nhdsWithin fun r hr => ⟨hr, trivial⟩⟩
      have tv0 := (hcont_v 0 (r₀, x) ⟨hr₀, trivial⟩).tendsto.comp hmap
      have tv1 := (hcont_v 1 (r₀, x) ⟨hr₀, trivial⟩).tendsto.comp hmap
      have tE0 := (hcont_Ec 0 (r₀, x) ⟨hr₀, trivial⟩).tendsto.comp hmap
      have tE1 := (hcont_Ec 1 (r₀, x) ⟨hr₀, trivial⟩).tendsto.comp hmap
      simp_rw [CCP.integrand_eq]
      exact (((((tv0.mul_const _).add (tv1.mul_const _)).const_add _).const_mul _).sub
        ((tE0.const_mul _).const_mul _)).sub ((tE1.const_mul _).const_mul _)
  -- Combine fixed-w continuity with uniform operator bound ‖L r‖ ≤ M
  obtain ⟨M, hM, hMb⟩ := CCP.main_bound hc1 hm tr H hH hψ
  have key : ∀ r : ℝ, ∃ T : Xmc c m →L[ℝ] ℝ, r ∈ Icc 0 H → ‖T‖ ≤ M ∧ ∀ w : Xmc c m,
      IntegrableOn (cylCoupledIntegrand tr w r ψ) (B0579.cell c) volume ∧
      T w = ∫ x in B0579.cell c, cylCoupledIntegrand tr w r ψ x := by
    intro r
    by_cases hr : r ∈ Icc 0 H
    · obtain ⟨T, hT, hT2⟩ := CCP.clm_of_bound (c := c) (m := m)
        (fun w => cylCoupledIntegrand tr ⇑w r ψ) M hM (fun w => (hMb r hr w).1)
        (fun w => (hMb r hr w).2)
        (fun w1 w2 => by
          filter_upwards [CCP.coe_add_ae w1 w2, CCP.K_add_ae hc1 hm w1 w2] with x h hK
          rw [CCP.integrand_eq, CCP.integrand_eq, CCP.integrand_eq, h, hK]
          simp only [PiLp.add_apply]
          ring)
        (fun a w => by
          filter_upwards [CCP.coe_smul_ae a w] with x h
          rw [CCP.integrand_eq, CCP.integrand_eq, h, CCP.K_smul hm a w x]
          simp only [PiLp.smul_apply, smul_eq_mul]
          ring)
      exact ⟨T, fun _ => ⟨hT, hT2⟩⟩
    · exact ⟨0, fun h => absurd h hr⟩
  choose L hL using key
  refine ContinuousOn.congr ?_ (fun r hr => ((hL r hr).2 (om r)).2.symm)
  intro r₀ hr₀
  rw [ContinuousWithinAt]
  have h1 : Tendsto (fun r => L r (om r₀)) (𝓝[Icc 0 H] r₀) (𝓝 (L r₀ (om r₀))) := by
    have hf := (hfixed (om r₀) r₀ hr₀).tendsto
    rw [← ((hL r₀ hr₀).2 (om r₀)).2] at hf
    refine hf.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact ((hL r hr).2 (om r₀)).2.symm
  have h2 : Tendsto (fun r => L r (om r - om r₀)) (𝓝[Icc 0 H] r₀) (𝓝 0) := by
    have hnorm0 : Tendsto (fun r => M * ‖om r - om r₀‖) (𝓝[Icc 0 H] r₀) (𝓝 0) := by
      have hconst : Tendsto (fun _ : ℝ => om r₀) (𝓝[Icc 0 H] r₀) (𝓝 (om r₀)) := tendsto_const_nhds
      have hw := ((hom r₀ hr₀).tendsto.sub hconst).norm
      rw [sub_self, norm_zero] at hw
      simpa using hw.const_mul M
    refine squeeze_zero_norm' ?_ hnorm0
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact ((L r).le_opNorm (om r - om r₀)).trans
      (mul_le_mul_of_nonneg_right (hL r hr).1 (norm_nonneg _))
  have hsum := h1.add h2
  rw [add_zero] at hsum
  refine hsum.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r _
  rw [← map_add, add_sub_cancel]

private theorem pd_zero_fun (j : Fin 2) : B0579.pd j (0 : B0579.Plane → ℝ) = 0 := by
  funext x
  unfold B0579.pd
  change fderiv ℝ (fun _ : B0579.Plane => (0 : ℝ)) x (B0579.dir j) = 0
  simp

private theorem pd_sub_fun {f g : B0579.Plane → ℝ} (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) (j : Fin 2) :
    B0579.pd j (fun y => f y - g y) = fun y => B0579.pd j f y - B0579.pd j g y := by
  funext x
  unfold B0579.pd
  rw [fderiv_fun_sub (hf x) (hg x)]
  simp

private theorem isCylTest_sub {c : ℝ} {f g : B0579.Plane → ℝ}
    (hf : B0579.IsCylTest c f) (hg : B0579.IsCylTest c g) :
    B0579.IsCylTest c (fun y => f y - g y) where
  smooth := hf.smooth.sub hg.smooth
  periodic x := by simp [hf.periodic x, hg.periodic x]
  band := by
    obtain ⟨R₁, hR₁⟩ := hf.band
    obtain ⟨R₂, hR₂⟩ := hg.band
    refine ⟨max R₁ R₂, fun x hx => ?_⟩
    rw [hR₁ x ((le_max_left _ _).trans_lt hx), hR₂ x ((le_max_right _ _).trans_lt hx), sub_self]

private theorem cylCoupledIntegrand_zero {ν c : ℝ} (tr : B0140.TrainSol ν c)
    (w : B0579.Plane → ℝ) (r : ℝ) :
    cylCoupledIntegrand tr w r 0 = 0 := by
  funext x
  change cylCoupledIntegrand tr w r 0 x = 0
  rw [CCP.integrand_eq, pd_zero_fun 0, pd_zero_fun 1, pd_zero_fun 0, pd_zero_fun 1]
  simp

private theorem cylCoupledIntegrand_sub {ν c : ℝ} (tr : B0140.TrainSol ν c)
    (w : B0579.Plane → ℝ) (r : ℝ) {ψ₁ ψ₂ : B0579.Plane → ℝ}
    (hψ₁ : B0579.IsCylTest c ψ₁) (hψ₂ : B0579.IsCylTest c ψ₂) (x : B0579.Plane) :
    cylCoupledIntegrand tr w r ψ₁ x - cylCoupledIntegrand tr w r ψ₂ x =
      cylCoupledIntegrand tr w r (fun y => ψ₁ y - ψ₂ y) x := by
  have hp0 := pd_sub_fun hψ₁.differentiable hψ₂.differentiable 0
  have hp1 := pd_sub_fun hψ₁.differentiable hψ₂.differentiable 1
  have hp00 : B0579.pd 0 (B0579.pd 0 (fun y => ψ₁ y - ψ₂ y)) =
      fun y => B0579.pd 0 (B0579.pd 0 ψ₁) y - B0579.pd 0 (B0579.pd 0 ψ₂) y := by
    rw [hp0]; exact pd_sub_fun (hψ₁.pd 0).differentiable (hψ₂.pd 0).differentiable 0
  have hp11 : B0579.pd 1 (B0579.pd 1 (fun y => ψ₁ y - ψ₂ y)) =
      fun y => B0579.pd 1 (B0579.pd 1 ψ₁) y - B0579.pd 1 (B0579.pd 1 ψ₂) y := by
    rw [hp1]; exact pd_sub_fun (hψ₁.pd 1).differentiable (hψ₂.pd 1).differentiable 1
  rw [CCP.integrand_eq, CCP.integrand_eq, CCP.integrand_eq, hp00, hp11, hp0, hp1]
  dsimp
  ring

private theorem existsUnique_grid_cell {H : ℝ} (hH : 0 < H) (M : ℕ) (hM : 0 < M)
    {r : ℝ} (hr : r ∈ Ioc 0 H) :
    ∃ k ∈ Finset.range M, r ∈ Ioc ((k : ℝ) * H / (M : ℝ)) (((k + 1 : ℕ) : ℝ) * H / (M : ℝ)) ∧
      ∀ j ∈ Finset.range M,
        r ∈ Ioc ((j : ℝ) * H / (M : ℝ)) (((j + 1 : ℕ) : ℝ) * H / (M : ℝ)) → j = k := by
  have hM_pos : 0 < (M : ℝ) := Nat.cast_pos.2 hM
  let t : ℕ → ℝ := fun k => (k : ℝ) * H / (M : ℝ)
  have ht_mono : StrictMono t := by
    intro i j hij
    dsimp [t]
    exact div_lt_div_of_pos_right (mul_lt_mul_of_pos_right (Nat.cast_lt.2 hij) hH) hM_pos
  have hex : ∀ m : ℕ, r ∈ Ioc 0 (t m) → ∃ k < m, r ∈ Ioc (t k) (t (k + 1)) := by
    intro m
    induction m with
    | zero =>
      intro h0
      simp [t] at h0
    | succ m ih =>
      intro hm1
      by_cases hle : r ≤ t m
      · obtain ⟨k, hkm, hkr⟩ := ih ⟨hm1.1, hle⟩
        exact ⟨k, Nat.lt_succ_of_lt hkm, hkr⟩
      · exact ⟨m, Nat.lt_succ_self m, ⟨not_le.1 hle, hm1.2⟩⟩
  have htM : t M = H := by
    dsimp [t]
    exact mul_div_cancel_left₀ H hM_pos.ne'
  obtain ⟨k, hkM, hkr⟩ := hex M (htM.symm ▸ hr)
  refine ⟨k, Finset.mem_range.2 hkM, hkr, fun j _ hjr => ?_⟩
  by_contra hjk
  rcases lt_or_gt_of_ne hjk with hlt | hgt
  · have hle : t (j + 1) ≤ t k := ht_mono.monotone (Nat.succ_le_of_lt hlt)
    linarith [hjr.2, hkr.1]
  · have hle : t (k + 1) ≤ t j := ht_mono.monotone (Nat.succ_le_of_lt hgt)
    linarith [hkr.2, hjr.1]

private theorem time_step_identity {m : ℝ} (hm : 1 / 2 < m) {p : Params}
    (hc1 : 1 ≤ p.c) (hH : 0 < p.H)
    {om f : ℝ → Xmc p.c m} (hom_cont : ContinuousOn om (Icc 0 p.H))
    (hf_int : IntegrableOn f (Ioc 0 p.H) volume)
    (hom_weak : ∀ φ : B0579.Plane → ℝ, B0579.IsCylTest p.c φ → ∀ s ∈ Icc 0 p.H,
      ∫ x in B0579.cell p.c, om s x * φ x =
        (∫ x in B0579.cell p.c, om 0 x * φ x) +
          ∫ r in (0 : ℝ)..s, ∫ x in B0579.cell p.c,
            (cylCoupledIntegrand p.train (om r) r φ x + f r x * φ x))
    {Φ : Coord → ℝ} {a b R : ℝ} (ha : 0 < a) (_hab : a ≤ b) (hbH : b < p.H) (hR : 0 < R)
    (hΦ_test : IsCoordTest Φ)
    (hΦ_box : tsupport Φ ⊆ Icc a b ×ˢ (Icc (-R) R ×ˢ Icc (-R) R)) :
    let φ := qPeriodize p.c Φ
    let φ_s := qPeriodize p.c (cpd 0 Φ)
    IntegrableOn (fun s => ∫ x in B0579.cell p.c, om s x * φ_s s x) (Icc a b) volume ∧
      IntegrableOn (fun s => ∫ x in B0579.cell p.c, cylCoupledIntegrand p.train (om s) s (φ s) x)
        (Icc a b) volume ∧
      IntegrableOn (fun s => ∫ x in B0579.cell p.c, f s x * φ s x) (Icc a b) volume ∧
      ∫ s in Icc a b,
        ((∫ x in B0579.cell p.c, om s x * φ_s s x) +
          (∫ x in B0579.cell p.c, cylCoupledIntegrand p.train (om s) s (φ s) x) +
          (∫ x in B0579.cell p.c, f s x * φ s x)) = 0 := by
  intro φ φ_s
  have hc0 : 0 < p.c := by linarith
  let Box : Set Coord := Icc a b ×ˢ (Icc (-R) R ×ˢ Icc (-R) R)
  have hΦ0_test : IsCoordTest (cpd 0 Φ) := planarTest_isCoordTest_partial hΦ_test (cdir 0)
  have hΦ1_test : IsCoordTest (cpd 1 Φ) := planarTest_isCoordTest_partial hΦ_test (cdir 1)
  have hΦ2_test : IsCoordTest (cpd 2 Φ) := planarTest_isCoordTest_partial hΦ_test (cdir 2)
  have hΦ11_test : IsCoordTest (cpd 1 (cpd 1 Φ)) := planarTest_isCoordTest_partial hΦ1_test (cdir 1)
  have hΦ22_test : IsCoordTest (cpd 2 (cpd 2 Φ)) := planarTest_isCoordTest_partial hΦ2_test (cdir 2)
  have hΦ0_box : tsupport (cpd 0 Φ) ⊆ Box := (tsupport_cpd_subset 0).trans hΦ_box
  have hΦ1_box : tsupport (cpd 1 Φ) ⊆ Box := (tsupport_cpd_subset 1).trans hΦ_box
  have hΦ2_box : tsupport (cpd 2 Φ) ⊆ Box := (tsupport_cpd_subset 2).trans hΦ_box
  have hΦ11_box : tsupport (cpd 1 (cpd 1 Φ)) ⊆ Box := (tsupport_cpd_subset 1).trans hΦ1_box
  have hΦ22_box : tsupport (cpd 2 (cpd 2 Φ)) ⊆ Box := (tsupport_cpd_subset 2).trans hΦ2_box
  obtain ⟨C1_raw, hC1_raw, hC1w_raw⟩ := CCP.exists_L1_const p.c m hm
  let C1 : ℝ := C1_raw + 1
  have hC1_pos : 0 < C1 := by linarith
  have hC1w : ∀ w : Xmc p.c m, eLpNorm (⇑w) 1 (volume.restrict (B0579.cell p.c)) ≤
      ENNReal.ofReal C1 * ‖w‖ₑ := by
    intro w
    refine (hC1w_raw w).trans ?_
    gcongr
    dsimp [C1]
    linarith
  obtain ⟨C_op_raw, hCop_nn, hCop_bd⟩ :=
    coupled_strip_bound_exists (m := m) hc1 hm hH.le hR.le p.train
  let C_op : ℝ := C_op_raw + 1
  have hCop_pos : 0 < C_op := by linarith
  obtain ⟨M_om0, hM_om0⟩ := isCompact_Icc.exists_bound_of_continuousOn hom_cont
  let M_om : ℝ := max 1 M_om0
  have hM_om_pos : 0 < M_om := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hom_bd : ∀ s ∈ Icc 0 p.H, ‖om s‖ ≤ M_om :=
    fun s hs => (hM_om0 s hs).trans (le_max_right _ _)
  obtain ⟨B_φ, hB_φ, hφ_bd⟩ := qPeriodize_uniform_bound (H := p.H) hc0 hΦ_test hΦ_box
  obtain ⟨B_s, hB_s, hφs_bd⟩ := qPeriodize_uniform_bound (H := p.H) hc0 hΦ0_test hΦ0_box
  obtain ⟨B_1, hB_1, hφ1_bd⟩ := qPeriodize_uniform_bound (H := p.H) hc0 hΦ1_test hΦ1_box
  obtain ⟨B_2, hB_2, hφ2_bd⟩ := qPeriodize_uniform_bound (H := p.H) hc0 hΦ2_test hΦ2_box
  obtain ⟨B_11, hB_11, hφ11_bd⟩ := qPeriodize_uniform_bound (H := p.H) hc0 hΦ11_test hΦ11_box
  obtain ⟨B_22, hB_22, hφ22_bd⟩ := qPeriodize_uniform_bound (H := p.H) hc0 hΦ22_test hΦ22_box
  let B_all : ℝ := B_φ + B_1 + B_2 + B_11 + B_22
  have hB_all_pos : 0 < B_all := by positivity
  have hφ_cyl : ∀ s, B0579.IsCylTest p.c (φ s) := fun s => isCylTest_qPeriodize hc0 hΦ_test s
  have hφs_cyl : ∀ s, B0579.IsCylTest p.c (φ_s s) := fun s => isCylTest_qPeriodize hc0 hΦ0_test s
  have hφ0 : φ 0 = 0 :=
    qPeriodize_eq_zero_of_s_notMem hΦ_box (fun h => absurd h.1 (not_le.2 ha))
  have hφH : φ p.H = 0 :=
    qPeriodize_eq_zero_of_s_notMem hΦ_box (fun h => absurd h.2 (not_le.2 hbH))
  -- Derivatives of φ s in terms of qPeriodize of cpd Φ
  have hpd0_φ : ∀ s, B0579.pd 0 (φ s) = qPeriodize p.c (cpd 1 Φ) s :=
    fun s => funext fun x => pd_qPeriodize hc0 hΦ_test s 0 x
  have hpd1_φ : ∀ s, B0579.pd 1 (φ s) = qPeriodize p.c (cpd 2 Φ) s :=
    fun s => funext fun x => pd_qPeriodize hc0 hΦ_test s 1 x
  have hpd00_φ : ∀ s, B0579.pd 0 (B0579.pd 0 (φ s)) = qPeriodize p.c (cpd 1 (cpd 1 Φ)) s := by
    intro s; rw [hpd0_φ s]; exact funext fun x => pd_qPeriodize hc0 hΦ1_test s 0 x
  have hpd11_φ : ∀ s, B0579.pd 1 (B0579.pd 1 (φ s)) = qPeriodize p.c (cpd 2 (cpd 2 Φ)) s := by
    intro s; rw [hpd1_φ s]; exact funext fun x => pd_qPeriodize hc0 hΦ2_test s 1 x
  -- Uniform strip bounds for φ s at any s ∈ Icc 0 p.H
  have hφ_strip_bd : ∀ s ∈ Icc 0 p.H, ∀ x : B0579.Plane, |x.1| ≤ p.c / 2 →
      |φ s x| ≤ B_all ∧ |B0579.pd 0 (φ s) x| ≤ B_all ∧ |B0579.pd 1 (φ s) x| ≤ B_all ∧
        |B0579.pd 0 (B0579.pd 0 (φ s)) x + B0579.pd 1 (B0579.pd 1 (φ s)) x| ≤ 2 * B_all := by
    intro s hs x hx1
    have b0 := hφ_bd s hs x hx1
    have b1 := hφ1_bd s hs x hx1
    have b2 := hφ2_bd s hs x hx1
    have b11 := hφ11_bd s hs x hx1
    have b22 := hφ22_bd s hs x hx1
    rw [hpd00_φ, hpd11_φ, hpd0_φ, hpd1_φ]
    refine ⟨by dsimp [B_all]; linarith, by dsimp [B_all]; linarith, by dsimp [B_all]; linarith, ?_⟩
    have hle := abs_add_le (qPeriodize p.c (cpd 1 (cpd 1 Φ)) s x)
      (qPeriodize p.c (cpd 2 (cpd 2 Φ)) s x)
    dsimp [B_all]; linarith
  have hφ_strip_van : ∀ s : ℝ, ∀ x : B0579.Plane, R < |x.2| →
      φ s x = 0 ∧ B0579.pd 0 (φ s) x = 0 ∧ B0579.pd 1 (φ s) x = 0 ∧
        B0579.pd 0 (B0579.pd 0 (φ s)) x + B0579.pd 1 (B0579.pd 1 (φ s)) x = 0 := by
    intro s x hx2
    rw [hpd00_φ, hpd11_φ, hpd0_φ, hpd1_φ]
    refine ⟨qPeriodize_eq_zero_of_eta_gt hΦ_box s hx2,
      qPeriodize_eq_zero_of_eta_gt hΦ1_box s hx2,
      qPeriodize_eq_zero_of_eta_gt hΦ2_box s hx2, ?_⟩
    rw [qPeriodize_eq_zero_of_eta_gt hΦ11_box s hx2,
      qPeriodize_eq_zero_of_eta_gt hΦ22_box s hx2, add_zero]
  -- Continuity of r ↦ ∫_cell w * φ_s r for fixed w ∈ Xmc p.c m
  have hcont_w_φs : ∀ w : Xmc p.c m,
      ContinuousOn (fun r => ∫ x in B0579.cell p.c, w x * φ_s r x) (Icc 0 p.H) := by
    intro w r₀ hr₀
    rw [ContinuousWithinAt, Metric.tendsto_nhds]
    intro ε hε
    let ε' : ℝ := ε / (2 * C1 * (‖w‖ + 1))
    have hε' : 0 < ε' := div_pos hε (by positivity)
    obtain ⟨δ, hδ, hmod⟩ := qPeriodize_uniform_continuity (H := p.H) hc0 hΦ0_test hΦ0_box hε'
    have hball : Icc 0 p.H ∩ Metric.ball r₀ δ ∈ 𝓝[Icc 0 p.H] r₀ :=
      inter_mem_nhdsWithin _ (Metric.ball_mem_nhds r₀ hδ)
    filter_upwards [hball] with r ⟨hr, hr_dist⟩
    rw [Metric.mem_ball, Real.dist_eq] at hr_dist
    rw [Real.dist_eq]
    let ψ_diff : B0579.Plane → ℝ := fun x => φ_s r x - φ_s r₀ x
    have hdiff_int1 := (source_strip_bound hm hB_s hC1_pos.le hC1w (hφs_cyl r).continuous.measurable
      (hφs_bd r hr) (fun x hx => qPeriodize_eq_zero_of_eta_gt hΦ0_box r hx) w).1
    have hdiff_int0 := (source_strip_bound hm hB_s hC1_pos.le hC1w (hφs_cyl r₀).continuous.measurable
      (hφs_bd r₀ hr₀) (fun x hx => qPeriodize_eq_zero_of_eta_gt hΦ0_box r₀ hx) w).1
    have hsub_eq : (∫ x in B0579.cell p.c, w x * φ_s r x) -
        (∫ x in B0579.cell p.c, w x * φ_s r₀ x) =
        ∫ x in B0579.cell p.c, w x * ψ_diff x := by
      rw [← integral_sub hdiff_int1 hdiff_int0]
      congr 1; funext x; dsimp [ψ_diff]; ring
    rw [hsub_eq]
    have hbd := (source_strip_bound hm hε' hC1_pos.le hC1w
      ((hφs_cyl r).continuous.sub (hφs_cyl r₀).continuous).measurable
      (fun x hx => hmod r hr r₀ hr₀ hr_dist x hx)
      (fun x hx => by
        dsimp [ψ_diff, φ_s]
        rw [qPeriodize_eq_zero_of_eta_gt hΦ0_box r hx,
          qPeriodize_eq_zero_of_eta_gt hΦ0_box r₀ hx, sub_self]) w).2
    rw [Real.norm_eq_abs] at hbd
    have hlt : C1 * ε' * ‖w‖ < ε := by
      calc C1 * ε' * ‖w‖ ≤ C1 * ε' * (‖w‖ + 1) := by gcongr; linarith
        _ = ε / 2 := by
            dsimp [ε']
            have hne : 2 * C1 * (‖w‖ + 1) ≠ 0 := by positivity
            field_simp [hne]
        _ < ε := half_lt_self hε
    exact lt_of_le_of_lt hbd hlt
  -- Fubini on Ioc t₁ t₂ ×ˢ cell for fixed w ∈ Xmc p.c m
  have hfub_w : ∀ {t₁ t₂ : ℝ}, 0 ≤ t₁ → t₁ ≤ t₂ → t₂ ≤ p.H → ∀ w : Xmc p.c m,
      ∫ x in B0579.cell p.c, w x * (φ t₂ x - φ t₁ x) =
        ∫ r in Ioc t₁ t₂, ∫ x in B0579.cell p.c, w x * φ_s r x := by
    intro t₁ t₂ ht₁ ht₁₂ ht₂ w
    have hwm : AEStronglyMeasurable (⇑w) (volume.restrict (B0579.cell p.c)) :=
      (Lp.aestronglyMeasurable w).mono_ac (B0579.ac_cellMeasure p.c m)
    have hF_aesm : AEStronglyMeasurable (Function.uncurry fun r x => w x * φ_s r x)
        ((volume.restrict (Ioc t₁ t₂)).prod (volume.restrict (B0579.cell p.c))) :=
      hwm.comp_snd.mul (continuous_qPeriodize_joint hc0 hΦ0_test).aestronglyMeasurable
    have hF_int : Integrable (Function.uncurry fun r x => w x * φ_s r x)
        ((volume.restrict (Ioc t₁ t₂)).prod (volume.restrict (B0579.cell p.c))) := by
      refine ⟨hF_aesm, ?_⟩
      rw [hasFiniteIntegral_iff_enorm, lintegral_prod _ hF_aesm.enorm]
      have hslice_le : ∀ r ∈ Ioc t₁ t₂,
          ∫⁻ x in B0579.cell p.c, ‖w x * φ_s r x‖ₑ ≤ ENNReal.ofReal (B_s * C1) * ‖w‖ₑ := by
        intro r hr
        have hr_Icc : r ∈ Icc 0 p.H := ⟨ht₁.trans hr.1.le, hr.2.trans ht₂⟩
        calc ∫⁻ x in B0579.cell p.c, ‖w x * φ_s r x‖ₑ
            ≤ ∫⁻ x in B0579.cell p.c, ENNReal.ofReal B_s * ‖w x‖ₑ := by
              refine setLIntegral_mono' (B0579.measurableSet_cell p.c) fun x hx => ?_
              have hx1 : |x.1| ≤ p.c / 2 := abs_le.2 ⟨hx.1.1, hx.1.2.le⟩
              rw [enorm_mul, mul_comm]; gcongr
              rw [← ofReal_norm]
              exact ENNReal.ofReal_le_ofReal (by simpa using hφs_bd r hr_Icc x hx1)
          _ = ENNReal.ofReal B_s * eLpNorm (⇑w) 1 (volume.restrict (B0579.cell p.c)) := by
              rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, eLpNorm_one_eq_lintegral_enorm]
          _ ≤ ENNReal.ofReal B_s * (ENNReal.ofReal C1 * ‖w‖ₑ) := by gcongr; exact hC1w w
          _ = ENNReal.ofReal (B_s * C1) * ‖w‖ₑ := by
              rw [ENNReal.ofReal_mul hB_s.le, mul_assoc]
      calc ∫⁻ r in Ioc t₁ t₂, ∫⁻ x in B0579.cell p.c, ‖w x * φ_s r x‖ₑ
          ≤ ∫⁻ _r in Ioc t₁ t₂, ENNReal.ofReal (B_s * C1) * ‖w‖ₑ :=
            setLIntegral_mono' measurableSet_Ioc hslice_le
        _ = (ENNReal.ofReal (B_s * C1) * ‖w‖ₑ) * volume (Ioc t₁ t₂) := by
            rw [setLIntegral_const]
        _ < ⊤ := ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top enorm_lt_top)
            (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top)
    rw [integral_integral_swap hF_int]
    refine setIntegral_congr_fun (B0579.measurableSet_cell p.c) fun x _ => ?_
    rw [qPeriodize_sub_eq_setIntegral_Ioc hc0 hΦ_test ht₁₂ x, ← integral_const_mul]
  -- Define target slice functions L1, L2, L3 and grid approximations F1, F2, F3
  let L1 : ℝ → ℝ := fun r => ∫ x in B0579.cell p.c, om r x * φ_s r x
  let L2 : ℝ → ℝ := fun r => ∫ x in B0579.cell p.c, cylCoupledIntegrand p.train (om r) r (φ r) x
  let L3 : ℝ → ℝ := fun r => ∫ x in B0579.cell p.c, f r x * φ r x
  let gridT : ℕ → ℕ → ℝ := fun n k => (k : ℝ) * p.H / ((n + 1 : ℕ) : ℝ)
  let F1 : ℕ → ℝ → ℝ := fun n r =>
    ∑ k ∈ Finset.range (n + 1),
      (Ioc (gridT n k) (gridT n (k + 1))).indicator
        (fun r' => ∫ x in B0579.cell p.c, om (gridT n (k + 1)) x * φ_s r' x) r
  let F2 : ℕ → ℝ → ℝ := fun n r =>
    ∑ k ∈ Finset.range (n + 1),
      (Ioc (gridT n k) (gridT n (k + 1))).indicator
        (fun r' => ∫ x in B0579.cell p.c, cylCoupledIntegrand p.train (om r') r' (φ (gridT n k)) x) r
  let F3 : ℕ → ℝ → ℝ := fun n r =>
    ∑ k ∈ Finset.range (n + 1),
      (Ioc (gridT n k) (gridT n (k + 1))).indicator
        (fun r' => ∫ x in B0579.cell p.c, f r' x * φ (gridT n k) x) r
  have hgrid_mem : ∀ n : ℕ, ∀ k ≤ n + 1, gridT n k ∈ Icc 0 p.H := by
    intro n k hk
    have hM_pos : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
    refine ⟨by dsimp [gridT]; positivity, ?_⟩
    dsimp [gridT]
    rw [div_le_iff₀ hM_pos]
    have hle : (k : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := Nat.cast_le.2 hk
    nlinarith
  have hgrid_le : ∀ n k : ℕ, gridT n k ≤ gridT n (k + 1) := by
    intro n k
    have hM_pos : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
    dsimp [gridT]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (Nat.cast_le.2 (Nat.le_succ k)) hH.le) hM_pos.le
  have hgrid_sub : ∀ n : ℕ, ∀ k < n + 1,
      Ioc (gridT n k) (gridT n (k + 1)) ⊆ Ioc 0 p.H := by
    intro n k hk r hr
    have h0 : 0 ≤ gridT n k := (hgrid_mem n k (Nat.le_of_lt hk)).1
    have h1 : gridT n (k + 1) ≤ p.H := (hgrid_mem n (k + 1) hk).2
    exact ⟨lt_of_le_of_lt h0 hr.1, hr.2.trans h1⟩
  -- Integrability and discrete sum identity for each n
  have hF_step : ∀ n : ℕ,
      IntegrableOn (F1 n) (Ioc 0 p.H) volume ∧
      IntegrableOn (F2 n) (Ioc 0 p.H) volume ∧
      IntegrableOn (F3 n) (Ioc 0 p.H) volume ∧
      (∫ r in Ioc 0 p.H, F1 n r) + (∫ r in Ioc 0 p.H, F2 n r) + (∫ r in Ioc 0 p.H, F3 n r) = 0 := by
    intro n
    let M : ℕ := n + 1
    have h1_k : ∀ k ∈ Finset.range M, IntegrableOn
        ((Ioc (gridT n k) (gridT n (k + 1))).indicator
          (fun r' => ∫ x in B0579.cell p.c, om (gridT n (k + 1)) x * φ_s r' x))
        (Ioc 0 p.H) volume := by
      intro k hk
      have hk_lt : k < M := Finset.mem_range.1 hk
      have hcont := hcont_w_φs (om (gridT n (k + 1)))
      have hint_Icc : IntegrableOn
          (fun r' => ∫ x in B0579.cell p.c, om (gridT n (k + 1)) x * φ_s r' x)
          (Icc 0 p.H) volume := hcont.integrableOn_Icc
      have hint_sub := hint_Icc.mono_set
        ((hgrid_sub n k hk_lt).trans Ioc_subset_Icc_self)
      exact (integrable_indicator_iff measurableSet_Ioc).2 hint_sub |>.integrableOn
    have h2_k : ∀ k ∈ Finset.range M, IntegrableOn
        ((Ioc (gridT n k) (gridT n (k + 1))).indicator
          (fun r' => ∫ x in B0579.cell p.c,
            cylCoupledIntegrand p.train (om r') r' (φ (gridT n k)) x))
        (Ioc 0 p.H) volume := by
      intro k hk
      have hk_lt : k < M := Finset.mem_range.1 hk
      have hcont := continuousOn_coupled_fixed_test hc1 hm hH.le p.train hom_cont (hφ_cyl (gridT n k))
      have hint_Icc : IntegrableOn
          (fun r' => ∫ x in B0579.cell p.c,
            cylCoupledIntegrand p.train (om r') r' (φ (gridT n k)) x)
          (Icc 0 p.H) volume := hcont.integrableOn_Icc
      have hint_sub := hint_Icc.mono_set
        ((hgrid_sub n k hk_lt).trans Ioc_subset_Icc_self)
      exact (integrable_indicator_iff measurableSet_Ioc).2 hint_sub |>.integrableOn
    have h3_k : ∀ k ∈ Finset.range M, IntegrableOn
        ((Ioc (gridT n k) (gridT n (k + 1))).indicator
          (fun r' => ∫ x in B0579.cell p.c, f r' x * φ (gridT n k) x))
        (Ioc 0 p.H) volume := by
      intro k hk
      have hk_lt : k < M := Finset.mem_range.1 hk
      obtain ⟨T_k, hT_k⟩ := sourcePairCLM (m := m) hm (hφ_cyl (gridT n k))
      have hint_Ioc : IntegrableOn (fun r' => ∫ x in B0579.cell p.c, f r' x * φ (gridT n k) x)
          (Ioc 0 p.H) volume :=
        (show IntegrableOn _ (Ioc 0 p.H) volume from T_k.integrable_comp hf_int).congr_fun
          (fun r' _ => (hT_k (f r')).2) measurableSet_Ioc
      have hint_sub := hint_Ioc.mono_set (hgrid_sub n k hk_lt)
      exact (integrable_indicator_iff measurableSet_Ioc).2 hint_sub |>.integrableOn
    have hF1_int : IntegrableOn (F1 n) (Ioc 0 p.H) volume := integrable_finsetSum _ h1_k
    have hF2_int : IntegrableOn (F2 n) (Ioc 0 p.H) volume := integrable_finsetSum _ h2_k
    have hF3_int : IntegrableOn (F3 n) (Ioc 0 p.H) volume := integrable_finsetSum _ h3_k
    refine ⟨hF1_int, hF2_int, hF3_int, ?_⟩
    rw [integral_finsetSum _ h1_k, integral_finsetSum _ h2_k, integral_finsetSum _ h3_k,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    let P : ℝ → ℝ → ℝ := fun u v => ∫ x in B0579.cell p.c, om u x * φ v x
    have hterm_eq : ∀ k ∈ Finset.range M,
        (∫ r in Ioc 0 p.H, (Ioc (gridT n k) (gridT n (k + 1))).indicator
          (fun r' => ∫ x in B0579.cell p.c, om (gridT n (k + 1)) x * φ_s r' x) r) +
        (∫ r in Ioc 0 p.H, (Ioc (gridT n k) (gridT n (k + 1))).indicator
          (fun r' => ∫ x in B0579.cell p.c,
            cylCoupledIntegrand p.train (om r') r' (φ (gridT n k)) x) r) +
        (∫ r in Ioc 0 p.H, (Ioc (gridT n k) (gridT n (k + 1))).indicator
          (fun r' => ∫ x in B0579.cell p.c, f r' x * φ (gridT n k) x) r) =
        P (gridT n (k + 1)) (gridT n (k + 1)) - P (gridT n k) (gridT n k) := by
      intro k hk
      have hk_lt : k < M := Finset.mem_range.1 hk
      have hsub := hgrid_sub n k hk_lt
      have hind_eq : ∀ g : ℝ → ℝ,
          ∫ r in Ioc 0 p.H, (Ioc (gridT n k) (gridT n (k + 1))).indicator g r =
            ∫ r in Ioc (gridT n k) (gridT n (k + 1)), g r := by
        intro g
        rw [setIntegral_indicator measurableSet_Ioc, inter_eq_self_of_subset_right hsub]
      rw [hind_eq, hind_eq, hind_eq]
      have htk_mem : gridT n k ∈ Icc 0 p.H := hgrid_mem n k (Nat.le_of_lt hk_lt)
      have htk1_mem : gridT n (k + 1) ∈ Icc 0 p.H := hgrid_mem n (k + 1) hk_lt
      have hle_k : gridT n k ≤ gridT n (k + 1) := hgrid_le n k
      -- First piece: time-difference of test at t_{k+1}
      have hI_fub := (hfub_w htk_mem.1 hle_k htk1_mem.2 (om (gridT n (k + 1)))).symm
      have hP_diff1 : ∫ x in B0579.cell p.c,
          om (gridT n (k + 1)) x * (φ (gridT n (k + 1)) x - φ (gridT n k) x) =
          P (gridT n (k + 1)) (gridT n (k + 1)) - P (gridT n (k + 1)) (gridT n k) := by
        have hi1 := (source_strip_bound hm hB_φ hC1_pos.le hC1w
          (hφ_cyl (gridT n (k + 1))).continuous.measurable (hφ_bd _ htk1_mem)
          (fun x hx => qPeriodize_eq_zero_of_eta_gt hΦ_box _ hx) (om (gridT n (k + 1)))).1
        have hi0 := (source_strip_bound hm hB_φ hC1_pos.le hC1w
          (hφ_cyl (gridT n k)).continuous.measurable (hφ_bd _ htk_mem)
          (fun x hx => qPeriodize_eq_zero_of_eta_gt hΦ_box _ hx) (om (gridT n (k + 1)))).1
        dsimp [P]
        rw [← integral_sub hi1 hi0]
        congr 1; funext x; ring
      -- Second + third piece: weak equation difference at ψ = φ(t_k)
      let ψk := φ (gridT n k)
      have hψk : B0579.IsCylTest p.c ψk := hφ_cyl (gridT n k)
      have hw1 := hom_weak ψk hψk (gridT n (k + 1)) htk1_mem
      have hw0 := hom_weak ψk hψk (gridT n k) htk_mem
      let g_rhs : ℝ → ℝ := fun r' => ∫ x in B0579.cell p.c,
        (cylCoupledIntegrand p.train (om r') r' ψk x + f r' x * ψk x)
      have hg2_Ioc : IntegrableOn
          (fun r' => ∫ x in B0579.cell p.c, cylCoupledIntegrand p.train (om r') r' ψk x)
          (Ioc 0 p.H) volume :=
        (continuousOn_coupled_fixed_test hc1 hm hH.le p.train hom_cont hψk).integrableOn_Icc.mono_set
          Ioc_subset_Icc_self
      obtain ⟨T_k, hT_k⟩ := sourcePairCLM (m := m) hm hψk
      have hg3_Ioc : IntegrableOn
          (fun r' => ∫ x in B0579.cell p.c, f r' x * ψk x) (Ioc 0 p.H) volume :=
        (show IntegrableOn _ (Ioc 0 p.H) volume from T_k.integrable_comp hf_int).congr_fun
          (fun r' _ => (hT_k (f r')).2) measurableSet_Ioc
      have hsplit_rhs : ∀ r' ∈ Ioc 0 p.H,
          g_rhs r' = (∫ x in B0579.cell p.c, cylCoupledIntegrand p.train (om r') r' ψk x) +
            (∫ x in B0579.cell p.c, f r' x * ψk x) := by
        intro r' hr'
        have hr'_Icc : r' ∈ Icc 0 p.H := ⟨hr'.1.le, hr'.2⟩
        have hc_int := (hCop_bd hB_all_pos hψk (hφ_strip_bd _ htk_mem)
          (hφ_strip_van _) r' hr'_Icc (om r')).1
        have hf_cell_int := (hT_k (f r')).1
        exact integral_add hc_int hf_cell_int
      have hg_Ioc : IntegrableOn g_rhs (Ioc 0 p.H) volume :=
        (intOn_add hg2_Ioc hg3_Ioc).congr_fun (fun r' hr' => (hsplit_rhs r' hr').symm)
          measurableSet_Ioc
      have hadj : (∫ r' in (0 : ℝ)..gridT n k, g_rhs r') +
          (∫ r' in gridT n k..gridT n (k + 1), g_rhs r') =
          ∫ r' in (0 : ℝ)..gridT n (k + 1), g_rhs r' := by
        refine intervalIntegral.integral_add_adjacent_intervals ?_ ?_
        · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le htk_mem.1]
          exact hg_Ioc.mono_set (Ioc_subset_Ioc_right htk_mem.2)
        · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hle_k]
          exact hg_Ioc.mono_set hsub
      have hP_diff2 : P (gridT n (k + 1)) (gridT n k) - P (gridT n k) (gridT n k) =
          (∫ r in Ioc (gridT n k) (gridT n (k + 1)),
            ∫ x in B0579.cell p.c, cylCoupledIntegrand p.train (om r) r ψk x) +
          (∫ r in Ioc (gridT n k) (gridT n (k + 1)),
            ∫ x in B0579.cell p.c, f r x * ψk x) := by
        have hsub_w : P (gridT n (k + 1)) (gridT n k) - P (gridT n k) (gridT n k) =
            ∫ r' in gridT n k..gridT n (k + 1), g_rhs r' := by
          dsimp [P]
          linarith [hw1, hw0, hadj]
        rw [hsub_w, intervalIntegral.integral_of_le hle_k,
          setIntegral_congr_fun measurableSet_Ioc (fun r' hr' => hsplit_rhs r' (hsub hr')),
          integral_add (hg2_Ioc.mono_set hsub) (hg3_Ioc.mono_set hsub)]
      rw [hI_fub, hP_diff1]
      linarith [hP_diff2]
    rw [Finset.sum_congr rfl hterm_eq,
      Finset.sum_range_sub (fun k => P (gridT n k) (gridT n k)) M]
    have ht0 : gridT n 0 = 0 := by simp [gridT]
    have htM : gridT n M = p.H := by
      dsimp [gridT, M]
      exact mul_div_cancel_left₀ p.H (by positivity)
    rw [ht0, htM]
    dsimp [P]
    rw [hφ0, hφH]
    simp
  -- Pointwise convergence and DCT on Ioc 0 p.H for F1, F2, F3
  have hgrid_mesh : Tendsto (fun n : ℕ => p.H / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  -- 1. F1 → L1
  have hF1_pt : ∀ r ∈ Ioc 0 p.H, Tendsto (fun n => F1 n r) atTop (𝓝 (L1 r)) := by
    intro r hr
    have hr_Icc : r ∈ Icc 0 p.H := ⟨hr.1.le, hr.2⟩
    rw [Metric.tendsto_atTop]
    intro ε hε
    let ε' : ℝ := ε / (2 * (C1 * B_s))
    have hε' : 0 < ε' := div_pos hε (by positivity)
    have hc_at := Metric.continuousWithinAt_iff.1 (hom_cont r hr_Icc) ε' hε'
    obtain ⟨δ, hδ, hom_mod⟩ := hc_at
    obtain ⟨N₀, hN₀⟩ := Metric.tendsto_atTop.1 hgrid_mesh δ hδ
    refine ⟨N₀, fun n hn => ?_⟩
    obtain ⟨k, hk, hkr, hk_uniq⟩ := existsUnique_grid_cell hH (n + 1) (Nat.succ_pos n) hr
    have hF1_val : F1 n r = ∫ x in B0579.cell p.c, om (gridT n (k + 1)) x * φ_s r x := by
      dsimp [F1]
      rw [Finset.sum_eq_single k]
      · exact Set.indicator_of_mem hkr _
      · intro j hj hjk
        exact Set.indicator_of_notMem (fun hjr => hjk (hk_uniq j hj hjr)) _
      · intro hnot; exact absurd hk hnot
    rw [hF1_val, Real.dist_eq]
    have htk1_Icc : gridT n (k + 1) ∈ Icc 0 p.H := hgrid_mem n (k + 1) (Finset.mem_range.1 hk)
    have hdist_r : dist (gridT n (k + 1)) r < δ := by
      rw [Real.dist_eq]
      have hstep : gridT n (k + 1) - gridT n k = p.H / ((n + 1 : ℕ) : ℝ) := by
        dsimp [gridT]; push_cast; ring
      have habs : |gridT n (k + 1) - r| ≤ p.H / ((n + 1 : ℕ) : ℝ) := by
        rw [abs_of_nonneg (by linarith [hkr.2])]
        linarith [hkr.1, hkr.2, hstep]
      have hlt_mesh : p.H / ((n + 1 : ℕ) : ℝ) < δ := by
        have h := hN₀ n hn
        rwa [Real.dist_eq, sub_zero,
          abs_of_pos (div_pos hH (by positivity : (0 : ℝ) < ((n + 1 : ℕ) : ℝ)))] at h
      exact lt_of_le_of_lt habs hlt_mesh
    have hom_lt : ‖om (gridT n (k + 1)) - om r‖ < ε' := by
      simpa [dist_eq_norm] using hom_mod htk1_Icc hdist_r
    have hi1 := (source_strip_bound hm hB_s hC1_pos.le hC1w (hφs_cyl r).continuous.measurable
      (hφs_bd r hr_Icc) (fun x hx => qPeriodize_eq_zero_of_eta_gt hΦ0_box r hx)
      (om (gridT n (k + 1)))).1
    have hi0 := (source_strip_bound hm hB_s hC1_pos.le hC1w (hφs_cyl r).continuous.measurable
      (hφs_bd r hr_Icc) (fun x hx => qPeriodize_eq_zero_of_eta_gt hΦ0_box r hx) (om r)).1
    have hsub_ae : (fun x => om (gridT n (k + 1)) x * φ_s r x - om r x * φ_s r x) =ᵐ[
        volume.restrict (B0579.cell p.c)]
        fun x => (om (gridT n (k + 1)) - om r) x * φ_s r x := by
      filter_upwards [(B0579.ac_cellMeasure p.c m).ae_le
        (Lp.coeFn_sub (om (gridT n (k + 1)) : B0579.X p.c m) (om r : B0579.X p.c m))]
        with x hx
      rw [hx, Pi.sub_apply]
      ring
    have heq_int : (∫ x in B0579.cell p.c, om (gridT n (k + 1)) x * φ_s r x) - L1 r =
        ∫ x in B0579.cell p.c, (om (gridT n (k + 1)) - om r) x * φ_s r x := by
      dsimp [L1]
      rw [← integral_sub hi1 hi0, integral_congr_ae hsub_ae]
      rfl
    rw [heq_int]
    have hbd := (source_strip_bound hm hB_s hC1_pos.le hC1w (hφs_cyl r).continuous.measurable
      (hφs_bd r hr_Icc) (fun x hx => qPeriodize_eq_zero_of_eta_gt hΦ0_box r hx)
      (om (gridT n (k + 1)) - om r)).2
    rw [Real.norm_eq_abs] at hbd
    calc |∫ x in B0579.cell p.c, (om (gridT n (k + 1)) - om r) x * φ_s r x|
        ≤ C1 * B_s * ‖om (gridT n (k + 1)) - om r‖ := hbd
      _ ≤ C1 * B_s * ε' := by gcongr
      _ = ε / 2 := by
          dsimp [ε']
          have hne : 2 * (C1 * B_s) ≠ 0 := by positivity
          field_simp [hne]
      _ < ε := half_lt_self hε
  -- 2. F2 → L2
  have hF2_pt : ∀ r ∈ Ioc 0 p.H, Tendsto (fun n => F2 n r) atTop (𝓝 (L2 r)) := by
    intro r hr
    have hr_Icc : r ∈ Icc 0 p.H := ⟨hr.1.le, hr.2⟩
    rw [Metric.tendsto_atTop]
    intro ε hε
    let ε' : ℝ := ε / (2 * (C_op * M_om))
    have hε' : 0 < ε' := div_pos hε (by positivity)
    obtain ⟨δ0, hδ0, hm0⟩ := qPeriodize_uniform_continuity (H := p.H) hc0 hΦ_test hΦ_box hε'
    obtain ⟨δ1, hδ1, hm1⟩ := qPeriodize_uniform_continuity (H := p.H) hc0 hΦ1_test hΦ1_box hε'
    obtain ⟨δ2, hδ2, hm2⟩ := qPeriodize_uniform_continuity (H := p.H) hc0 hΦ2_test hΦ2_box hε'
    obtain ⟨δ11, hδ11, hm11⟩ := qPeriodize_uniform_continuity (H := p.H) hc0 hΦ11_test hΦ11_box hε'
    obtain ⟨δ22, hδ22, hm22⟩ := qPeriodize_uniform_continuity (H := p.H) hc0 hΦ22_test hΦ22_box hε'
    let δ : ℝ := min δ0 (min δ1 (min δ2 (min δ11 δ22)))
    have hδ : 0 < δ := lt_min hδ0 (lt_min hδ1 (lt_min hδ2 (lt_min hδ11 hδ22)))
    obtain ⟨N₀, hN₀⟩ := Metric.tendsto_atTop.1 hgrid_mesh δ hδ
    refine ⟨N₀, fun n hn => ?_⟩
    obtain ⟨k, hk, hkr, hk_uniq⟩ := existsUnique_grid_cell hH (n + 1) (Nat.succ_pos n) hr
    have hF2_val : F2 n r =
        ∫ x in B0579.cell p.c, cylCoupledIntegrand p.train (om r) r (φ (gridT n k)) x := by
      dsimp [F2]
      rw [Finset.sum_eq_single k]
      · exact Set.indicator_of_mem hkr _
      · intro j hj hjk
        exact Set.indicator_of_notMem (fun hjr => hjk (hk_uniq j hj hjr)) _
      · intro hnot; exact absurd hk hnot
    rw [hF2_val, Real.dist_eq]
    have htk_Icc : gridT n k ∈ Icc 0 p.H :=
      hgrid_mem n k (Nat.le_of_lt (Finset.mem_range.1 hk))
    have hdist_r : |gridT n k - r| < δ := by
      have hstep : gridT n (k + 1) - gridT n k = p.H / ((n + 1 : ℕ) : ℝ) := by
        dsimp [gridT]; push_cast; ring
      have habs : |gridT n k - r| ≤ p.H / ((n + 1 : ℕ) : ℝ) := by
        rw [abs_sub_comm, abs_of_pos (by linarith [hkr.1])]
        linarith [hkr.1, hkr.2, hstep]
      have hlt_mesh : p.H / ((n + 1 : ℕ) : ℝ) < δ := by
        have h := hN₀ n hn
        rwa [Real.dist_eq, sub_zero,
          abs_of_pos (div_pos hH (by positivity : (0 : ℝ) < ((n + 1 : ℕ) : ℝ)))] at h
      exact lt_of_le_of_lt habs hlt_mesh
    let ψd : B0579.Plane → ℝ := fun y => φ (gridT n k) y - φ r y
    have hψd : B0579.IsCylTest p.c ψd := isCylTest_sub (hφ_cyl (gridT n k)) (hφ_cyl r)
    have hp0 : B0579.pd 0 ψd = fun y => B0579.pd 0 (φ (gridT n k)) y - B0579.pd 0 (φ r) y :=
      pd_sub_fun (hφ_cyl (gridT n k)).differentiable (hφ_cyl r).differentiable 0
    have hp1 : B0579.pd 1 ψd = fun y => B0579.pd 1 (φ (gridT n k)) y - B0579.pd 1 (φ r) y :=
      pd_sub_fun (hφ_cyl (gridT n k)).differentiable (hφ_cyl r).differentiable 1
    have hp00_f : B0579.pd 0 (B0579.pd 0 ψd) =
        fun y => B0579.pd 0 (B0579.pd 0 (φ (gridT n k))) y -
          B0579.pd 0 (B0579.pd 0 (φ r)) y := by
      rw [hp0]
      exact pd_sub_fun ((hφ_cyl (gridT n k)).pd 0).differentiable ((hφ_cyl r).pd 0).differentiable 0
    have hp11_f : B0579.pd 1 (B0579.pd 1 ψd) =
        fun y => B0579.pd 1 (B0579.pd 1 (φ (gridT n k))) y -
          B0579.pd 1 (B0579.pd 1 (φ r)) y := by
      rw [hp1]
      exact pd_sub_fun ((hφ_cyl (gridT n k)).pd 1).differentiable ((hφ_cyl r).pd 1).differentiable 1
    have hi1 := (hCop_bd hB_all_pos (hφ_cyl (gridT n k)) (hφ_strip_bd _ htk_Icc)
      (hφ_strip_van _) r hr_Icc (om r)).1
    have hi0 := (hCop_bd hB_all_pos (hφ_cyl r) (hφ_strip_bd _ hr_Icc)
      (hφ_strip_van _) r hr_Icc (om r)).1
    have heq_int : (∫ x in B0579.cell p.c, cylCoupledIntegrand p.train (om r) r (φ (gridT n k)) x) -
        L2 r = ∫ x in B0579.cell p.c, cylCoupledIntegrand p.train (om r) r ψd x := by
      dsimp [L2]
      rw [← integral_sub hi1 hi0]
      congr 1; funext x
      exact cylCoupledIntegrand_sub p.train (om r) r (hφ_cyl (gridT n k)) (hφ_cyl r) x
    rw [heq_int]
    have hψd_bd : ∀ x : B0579.Plane, |x.1| ≤ p.c / 2 →
        |ψd x| ≤ ε' ∧ |B0579.pd 0 ψd x| ≤ ε' ∧ |B0579.pd 1 ψd x| ≤ ε' ∧
          |B0579.pd 0 (B0579.pd 0 ψd) x + B0579.pd 1 (B0579.pd 1 ψd) x| ≤ 2 * ε' := by
      intro x hx1
      have hp00 : B0579.pd 0 (B0579.pd 0 ψd) x =
          qPeriodize p.c (cpd 1 (cpd 1 Φ)) (gridT n k) x -
            qPeriodize p.c (cpd 1 (cpd 1 Φ)) r x := by
        rw [congr_fun hp00_f x, hpd00_φ, hpd00_φ]
      have hp11 : B0579.pd 1 (B0579.pd 1 ψd) x =
          qPeriodize p.c (cpd 2 (cpd 2 Φ)) (gridT n k) x -
            qPeriodize p.c (cpd 2 (cpd 2 Φ)) r x := by
        rw [congr_fun hp11_f x, hpd11_φ, hpd11_φ]
      have d0 : |gridT n k - r| < δ0 := hdist_r.trans_le (min_le_left _ _)
      have d1 : |gridT n k - r| < δ1 :=
        hdist_r.trans_le ((min_le_right _ _).trans (min_le_left _ _))
      have d2 : |gridT n k - r| < δ2 :=
        hdist_r.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
      have d11 : |gridT n k - r| < δ11 :=
        hdist_r.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans
          ((min_le_right _ _).trans (min_le_left _ _))))
      have d22 : |gridT n k - r| < δ22 :=
        hdist_r.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans
          ((min_le_right _ _).trans (min_le_right _ _))))
      refine ⟨hm0 _ htk_Icc _ hr_Icc d0 x hx1, ?_, ?_, ?_⟩
      · rw [congr_fun hp0 x, hpd0_φ, hpd0_φ]; exact hm1 _ htk_Icc _ hr_Icc d1 x hx1
      · rw [congr_fun hp1 x, hpd1_φ, hpd1_φ]; exact hm2 _ htk_Icc _ hr_Icc d2 x hx1
      · rw [hp00, hp11]
        have b11 := hm11 _ htk_Icc _ hr_Icc d11 x hx1
        have b22 := hm22 _ htk_Icc _ hr_Icc d22 x hx1
        have hle := abs_add_le
          (qPeriodize p.c (cpd 1 (cpd 1 Φ)) (gridT n k) x - qPeriodize p.c (cpd 1 (cpd 1 Φ)) r x)
          (qPeriodize p.c (cpd 2 (cpd 2 Φ)) (gridT n k) x - qPeriodize p.c (cpd 2 (cpd 2 Φ)) r x)
        linarith
    have hψd_van : ∀ x : B0579.Plane, R < |x.2| →
        ψd x = 0 ∧ B0579.pd 0 ψd x = 0 ∧ B0579.pd 1 ψd x = 0 ∧
          B0579.pd 0 (B0579.pd 0 ψd) x + B0579.pd 1 (B0579.pd 1 ψd) x = 0 := by
      intro x hx2
      obtain ⟨v0k, v1k, v2k, vlk⟩ := hφ_strip_van (gridT n k) x hx2
      obtain ⟨v0r, v1r, v2r, vlr⟩ := hφ_strip_van r x hx2
      refine ⟨by dsimp [ψd]; rw [v0k, v0r, sub_self], ?_, ?_, ?_⟩
      · rw [congr_fun hp0 x, v1k, v1r, sub_self]
      · rw [congr_fun hp1 x, v2k, v2r, sub_self]
      · rw [congr_fun hp00_f x, congr_fun hp11_f x]; linarith
    have hbd := (hCop_bd hε' hψd hψd_bd hψd_van r hr_Icc (om r)).2
    rw [Real.norm_eq_abs] at hbd
    calc |∫ x in B0579.cell p.c, cylCoupledIntegrand p.train (om r) r ψd x|
        ≤ C_op_raw * ε' * ‖om r‖ := hbd
      _ ≤ C_op * ε' * M_om := by
          refine mul_le_mul (mul_le_mul_of_nonneg_right (by dsimp [C_op]; linarith) hε'.le)
            (hom_bd r hr_Icc) (norm_nonneg _) (by positivity)
      _ = ε / 2 := by
          dsimp [ε']
          have hne : 2 * (C_op * M_om) ≠ 0 := by positivity
          field_simp [hne]
      _ < ε := half_lt_self hε
  -- 3. F3 → L3
  have hF3_pt : ∀ r ∈ Ioc 0 p.H, Tendsto (fun n => F3 n r) atTop (𝓝 (L3 r)) := by
    intro r hr
    have hr_Icc : r ∈ Icc 0 p.H := ⟨hr.1.le, hr.2⟩
    rw [Metric.tendsto_atTop]
    intro ε hε
    let ε' : ℝ := ε / (2 * C1 * (‖f r‖ + 1))
    have hε' : 0 < ε' := div_pos hε (by positivity)
    obtain ⟨δ, hδ, hm0⟩ := qPeriodize_uniform_continuity (H := p.H) hc0 hΦ_test hΦ_box hε'
    obtain ⟨N₀, hN₀⟩ := Metric.tendsto_atTop.1 hgrid_mesh δ hδ
    refine ⟨N₀, fun n hn => ?_⟩
    obtain ⟨k, hk, hkr, hk_uniq⟩ := existsUnique_grid_cell hH (n + 1) (Nat.succ_pos n) hr
    have hF3_val : F3 n r = ∫ x in B0579.cell p.c, f r x * φ (gridT n k) x := by
      dsimp [F3]
      rw [Finset.sum_eq_single k]
      · exact Set.indicator_of_mem hkr _
      · intro j hj hjk
        exact Set.indicator_of_notMem (fun hjr => hjk (hk_uniq j hj hjr)) _
      · intro hnot; exact absurd hk hnot
    rw [hF3_val, Real.dist_eq]
    have htk_Icc : gridT n k ∈ Icc 0 p.H :=
      hgrid_mem n k (Nat.le_of_lt (Finset.mem_range.1 hk))
    have hdist_r : |gridT n k - r| < δ := by
      have hstep : gridT n (k + 1) - gridT n k = p.H / ((n + 1 : ℕ) : ℝ) := by
        dsimp [gridT]; push_cast; ring
      have habs : |gridT n k - r| ≤ p.H / ((n + 1 : ℕ) : ℝ) := by
        rw [abs_sub_comm, abs_of_pos (by linarith [hkr.1])]
        linarith [hkr.1, hkr.2, hstep]
      have hlt_mesh : p.H / ((n + 1 : ℕ) : ℝ) < δ := by
        have h := hN₀ n hn
        rwa [Real.dist_eq, sub_zero,
          abs_of_pos (div_pos hH (by positivity : (0 : ℝ) < ((n + 1 : ℕ) : ℝ)))] at h
      exact lt_of_le_of_lt habs hlt_mesh
    let ψd : B0579.Plane → ℝ := fun y => φ (gridT n k) y - φ r y
    have hi1 := (source_strip_bound hm hB_φ hC1_pos.le hC1w
      (hφ_cyl (gridT n k)).continuous.measurable (hφ_bd _ htk_Icc)
      (fun x hx => qPeriodize_eq_zero_of_eta_gt hΦ_box _ hx) (f r)).1
    have hi0 := (source_strip_bound hm hB_φ hC1_pos.le hC1w
      (hφ_cyl r).continuous.measurable (hφ_bd _ hr_Icc)
      (fun x hx => qPeriodize_eq_zero_of_eta_gt hΦ_box _ hx) (f r)).1
    have heq_int : (∫ x in B0579.cell p.c, f r x * φ (gridT n k) x) - L3 r =
        ∫ x in B0579.cell p.c, f r x * ψd x := by
      dsimp [L3]
      rw [← integral_sub hi1 hi0]
      congr 1; funext x; dsimp [ψd]; ring
    rw [heq_int]
    have hbd := (source_strip_bound hm hε' hC1_pos.le hC1w
      ((hφ_cyl (gridT n k)).continuous.sub (hφ_cyl r).continuous).measurable
      (fun x hx => hm0 _ htk_Icc _ hr_Icc hdist_r x hx)
      (fun x hx => by
        dsimp [ψd, φ]
        rw [qPeriodize_eq_zero_of_eta_gt hΦ_box _ hx,
          qPeriodize_eq_zero_of_eta_gt hΦ_box _ hx, sub_self]) (f r)).2
    rw [Real.norm_eq_abs] at hbd
    calc |∫ x in B0579.cell p.c, f r x * ψd x|
        ≤ C1 * ε' * ‖f r‖ := hbd
      _ ≤ C1 * ε' * (‖f r‖ + 1) := by gcongr; linarith
      _ = ε / 2 := by
          dsimp [ε']
          have hne : 2 * C1 * (‖f r‖ + 1) ≠ 0 := by positivity
          field_simp [hne]
      _ < ε := half_lt_self hε
  -- Dominating bounds on Ioc 0 p.H
  have hIoc_fin : volume (Ioc 0 p.H) < ⊤ := by rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top
  have hbd1_int : IntegrableOn (fun _ : ℝ => C1 * B_s * M_om) (Ioc 0 p.H) volume :=
    integrableOn_const (hs := hIoc_fin.ne)
  have hbd2_int : IntegrableOn (fun _ : ℝ => C_op_raw * B_all * M_om) (Ioc 0 p.H) volume :=
    integrableOn_const (hs := hIoc_fin.ne)
  have hbd3_int : IntegrableOn (fun r : ℝ => C1 * B_φ * ‖f r‖) (Ioc 0 p.H) volume :=
    hf_int.norm.const_mul (C1 * B_φ)
  have hF1_le : ∀ n : ℕ, ∀ r ∈ Ioc 0 p.H, ‖F1 n r‖ ≤ C1 * B_s * M_om := by
    intro n r hr
    have hr_Icc : r ∈ Icc 0 p.H := ⟨hr.1.le, hr.2⟩
    obtain ⟨k, hk, hkr, hk_uniq⟩ := existsUnique_grid_cell hH (n + 1) (Nat.succ_pos n) hr
    have hval : F1 n r = ∫ x in B0579.cell p.c, om (gridT n (k + 1)) x * φ_s r x := by
      dsimp [F1]; rw [Finset.sum_eq_single k]
      · exact Set.indicator_of_mem hkr _
      · intro j hj hjk; exact Set.indicator_of_notMem (fun hjr => hjk (hk_uniq j hj hjr)) _
      · intro hnot; exact absurd hk hnot
    rw [hval]
    have htk1_Icc : gridT n (k + 1) ∈ Icc 0 p.H := hgrid_mem n (k + 1) (Finset.mem_range.1 hk)
    exact ((source_strip_bound hm hB_s hC1_pos.le hC1w (hφs_cyl r).continuous.measurable
      (hφs_bd r hr_Icc) (fun x hx => qPeriodize_eq_zero_of_eta_gt hΦ0_box r hx)
      (om (gridT n (k + 1)))).2).trans
      (mul_le_mul_of_nonneg_left (hom_bd _ htk1_Icc) (by positivity))
  have hF2_le : ∀ n : ℕ, ∀ r ∈ Ioc 0 p.H, ‖F2 n r‖ ≤ C_op_raw * B_all * M_om := by
    intro n r hr
    have hr_Icc : r ∈ Icc 0 p.H := ⟨hr.1.le, hr.2⟩
    obtain ⟨k, hk, hkr, hk_uniq⟩ := existsUnique_grid_cell hH (n + 1) (Nat.succ_pos n) hr
    have hval : F2 n r =
        ∫ x in B0579.cell p.c, cylCoupledIntegrand p.train (om r) r (φ (gridT n k)) x := by
      dsimp [F2]; rw [Finset.sum_eq_single k]
      · exact Set.indicator_of_mem hkr _
      · intro j hj hjk; exact Set.indicator_of_notMem (fun hjr => hjk (hk_uniq j hj hjr)) _
      · intro hnot; exact absurd hk hnot
    rw [hval]
    have htk_Icc : gridT n k ∈ Icc 0 p.H :=
      hgrid_mem n k (Nat.le_of_lt (Finset.mem_range.1 hk))
    exact ((hCop_bd hB_all_pos (hφ_cyl (gridT n k)) (hφ_strip_bd _ htk_Icc)
      (hφ_strip_van _) r hr_Icc (om r)).2).trans
      (mul_le_mul_of_nonneg_left (hom_bd r hr_Icc) (by positivity))
  have hF3_le : ∀ n : ℕ, ∀ r ∈ Ioc 0 p.H, ‖F3 n r‖ ≤ C1 * B_φ * ‖f r‖ := by
    intro n r hr
    obtain ⟨k, hk, hkr, hk_uniq⟩ := existsUnique_grid_cell hH (n + 1) (Nat.succ_pos n) hr
    have hval : F3 n r = ∫ x in B0579.cell p.c, f r x * φ (gridT n k) x := by
      dsimp [F3]; rw [Finset.sum_eq_single k]
      · exact Set.indicator_of_mem hkr _
      · intro j hj hjk; exact Set.indicator_of_notMem (fun hjr => hjk (hk_uniq j hj hjr)) _
      · intro hnot; exact absurd hk hnot
    rw [hval]
    have htk_Icc : gridT n k ∈ Icc 0 p.H :=
      hgrid_mem n k (Nat.le_of_lt (Finset.mem_range.1 hk))
    exact (source_strip_bound hm hB_φ hC1_pos.le hC1w
      (hφ_cyl (gridT n k)).continuous.measurable (hφ_bd _ htk_Icc)
      (fun x hx => qPeriodize_eq_zero_of_eta_gt hΦ_box _ hx) (f r)).2
  -- Integrability of L1, L2, L3 on Ioc 0 p.H and DCT
  have hL1_aesm : AEStronglyMeasurable L1 (volume.restrict (Ioc 0 p.H)) :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun n => (hF_step n).1.1)
      ((ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall hF1_pt))
  have hL2_aesm : AEStronglyMeasurable L2 (volume.restrict (Ioc 0 p.H)) :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun n => (hF_step n).2.1.1)
      ((ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall hF2_pt))
  have hL3_aesm : AEStronglyMeasurable L3 (volume.restrict (Ioc 0 p.H)) :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun n => (hF_step n).2.2.1.1)
      ((ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall hF3_pt))
  have hL1_Ioc : IntegrableOn L1 (Ioc 0 p.H) volume := by
    refine hbd1_int.mono' hL1_aesm
      ((ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun r hr => ?_))
    have hr_Icc : r ∈ Icc 0 p.H := ⟨hr.1.le, hr.2⟩
    exact ((source_strip_bound hm hB_s hC1_pos.le hC1w (hφs_cyl r).continuous.measurable
      (hφs_bd r hr_Icc) (fun x hx => qPeriodize_eq_zero_of_eta_gt hΦ0_box r hx) (om r)).2).trans
      (mul_le_mul_of_nonneg_left (hom_bd r hr_Icc) (by positivity))
  have hL2_Ioc : IntegrableOn L2 (Ioc 0 p.H) volume := by
    refine hbd2_int.mono' hL2_aesm
      ((ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun r hr => ?_))
    have hr_Icc : r ∈ Icc 0 p.H := ⟨hr.1.le, hr.2⟩
    exact ((hCop_bd hB_all_pos (hφ_cyl r) (hφ_strip_bd r hr_Icc)
      (hφ_strip_van r) r hr_Icc (om r)).2).trans
      (mul_le_mul_of_nonneg_left (hom_bd r hr_Icc) (by positivity))
  have hL3_Ioc : IntegrableOn L3 (Ioc 0 p.H) volume := by
    refine hbd3_int.mono' hL3_aesm
      ((ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun r hr => ?_))
    have hr_Icc : r ∈ Icc 0 p.H := ⟨hr.1.le, hr.2⟩
    exact (source_strip_bound hm hB_φ hC1_pos.le hC1w (hφ_cyl r).continuous.measurable
      (hφ_bd r hr_Icc) (fun x hx => qPeriodize_eq_zero_of_eta_gt hΦ_box r hx) (f r)).2
  have htend1 : Tendsto (fun n => ∫ r in Ioc 0 p.H, F1 n r) atTop (𝓝 (∫ r in Ioc 0 p.H, L1 r)) :=
    tendsto_integral_of_dominated_convergence (fun _ => C1 * B_s * M_om)
      (fun n => (hF_step n).1.1) hbd1_int
      (fun n => (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall (hF1_le n)))
      ((ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall hF1_pt))
  have htend2 : Tendsto (fun n => ∫ r in Ioc 0 p.H, F2 n r) atTop (𝓝 (∫ r in Ioc 0 p.H, L2 r)) :=
    tendsto_integral_of_dominated_convergence (fun _ => C_op_raw * B_all * M_om)
      (fun n => (hF_step n).2.1.1) hbd2_int
      (fun n => (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall (hF2_le n)))
      ((ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall hF2_pt))
  have htend3 : Tendsto (fun n => ∫ r in Ioc 0 p.H, F3 n r) atTop (𝓝 (∫ r in Ioc 0 p.H, L3 r)) :=
    tendsto_integral_of_dominated_convergence (fun r => C1 * B_φ * ‖f r‖)
      (fun n => (hF_step n).2.2.1.1) hbd3_int
      (fun n => (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall (hF3_le n)))
      ((ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall hF3_pt))
  have htend_sum := (htend1.add htend2).add htend3
  have hconst0 : (fun n => (∫ r in Ioc 0 p.H, F1 n r) + (∫ r in Ioc 0 p.H, F2 n r) +
      (∫ r in Ioc 0 p.H, F3 n r)) = fun _ => (0 : ℝ) :=
    funext fun n => (hF_step n).2.2.2
  rw [hconst0] at htend_sum
  have hsum_Ioc : (∫ r in Ioc 0 p.H, L1 r) + (∫ r in Ioc 0 p.H, L2 r) +
      (∫ r in Ioc 0 p.H, L3 r) = 0 :=
    (tendsto_nhds_unique htend_sum tendsto_const_nhds)
  have hsub_ab : Icc a b ⊆ Ioc 0 p.H :=
    fun s hs => ⟨lt_of_lt_of_le ha hs.1, hs.2.trans hbH.le⟩
  refine ⟨hL1_Ioc.mono_set hsub_ab, hL2_Ioc.mono_set hsub_ab, hL3_Ioc.mono_set hsub_ab, ?_⟩
  have hIoc_total : ∫ s in Ioc 0 p.H, (L1 s + L2 s + L3 s) = 0 := by
    rw [integral_add (intOn_add hL1_Ioc hL2_Ioc) hL3_Ioc, integral_add hL1_Ioc hL2_Ioc]
    exact hsum_Ioc
  rw [← hIoc_total]
  refine (setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioc hsub_ab ?_).symm
  intro s ⟨_, hs_not⟩
  have hφ_zero : φ s = 0 := qPeriodize_eq_zero_of_s_notMem hΦ_box hs_not
  have hφs_zero : φ_s s = 0 := qPeriodize_eq_zero_of_s_notMem hΦ0_box hs_not
  rw [hφ_zero, hφs_zero, cylCoupledIntegrand_zero]
  simp

/-! ## 4. Coordinate unfolding and fixed-slice identities for `meridTranspose` and `flatBv` -/

private theorem summable_of_q_vanish {c R : ℝ} (hc : 0 < c) {α : Coord → ℝ}
    (hα : ∀ x : Coord, R < |x.2.1| → α x = 0) (s : ℝ) (z : B0579.Plane) :
    Summable (fun k : ℤ => α (s, (z.1 + (k : ℝ) * c, z.2))) := by
  obtain ⟨M, hM⟩ := exists_nat_gt ((|z.1| + R) / c + 1)
  refine summable_of_ne_finset_zero (s := Finset.Icc (-(M : ℤ)) (M : ℤ)) fun k hk => ?_
  apply hα
  dsimp
  rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hk
  have hk_abs : (M : ℝ) + 1 ≤ |(k : ℝ)| := by
    have hk_int : (M : ℤ) + 1 ≤ |k| := by
      rcases hk with hk | hk
      · rw [abs_of_neg (by omega)]; omega
      · rw [abs_of_nonneg (by omega)]; omega
    have hk_r : ((M : ℤ) + 1 : ℝ) ≤ (|k| : ℝ) := by exact_mod_cast hk_int
    simpa [Int.cast_abs] using hk_r
  have h1 : |z.1| + R + c < ((M : ℝ) + 1) * c := by
    have hm := mul_lt_mul_of_pos_right hM hc
    have hdiv : ((|z.1| + R) / c + 1) * c = |z.1| + R + c := by field_simp [hc.ne']
    linarith
  have h2 : ((M : ℝ) + 1) * c ≤ |(k : ℝ)| * c := mul_le_mul_of_nonneg_right hk_abs hc.le
  have h3 : |(k : ℝ)| * c - |z.1| ≤ |z.1 + (k : ℝ) * c| := by
    have hsub := abs_sub_abs_le_abs_add ((k : ℝ) * c) z.1
    rw [add_comm, abs_mul, abs_of_pos hc] at hsub
    linarith
  linarith

private theorem qPeriodize_neg (c : ℝ) (α : Coord → ℝ) (s : ℝ) (z : B0579.Plane) :
    qPeriodize c (fun x => -α x) s z = -qPeriodize c α s z := by
  unfold qPeriodize
  exact tsum_neg

private theorem qPeriodize_const_mul (c r : ℝ) (α : Coord → ℝ) (s : ℝ) (z : B0579.Plane) :
    qPeriodize c (fun x => r * α x) s z = r * qPeriodize c α s z := by
  unfold qPeriodize
  exact tsum_mul_left

private theorem qPeriodize_add {c R : ℝ} (hc : 0 < c) {α β : Coord → ℝ}
    (hα : ∀ x : Coord, R < |x.2.1| → α x = 0)
    (hβ : ∀ x : Coord, R < |x.2.1| → β x = 0)
    (s : ℝ) (z : B0579.Plane) :
    qPeriodize c (fun x => α x + β x) s z = qPeriodize c α s z + qPeriodize c β s z := by
  unfold qPeriodize
  exact (summable_of_q_vanish hc hα s z).tsum_add (summable_of_q_vanish hc hβ s z)

private theorem qPeriodize_sub {c R : ℝ} (hc : 0 < c) {α β : Coord → ℝ}
    (hα : ∀ x : Coord, R < |x.2.1| → α x = 0)
    (hβ : ∀ x : Coord, R < |x.2.1| → β x = 0)
    (s : ℝ) (z : B0579.Plane) :
    qPeriodize c (fun x => α x - β x) s z = qPeriodize c α s z - qPeriodize c β s z := by
  unfold qPeriodize
  exact (summable_of_q_vanish hc hα s z).tsum_sub (summable_of_q_vanish hc hβ s z)

private theorem qPeriodize_mul_periodic {c : ℝ} {coef β : Coord → ℝ} {s : ℝ}
    (hper : ∀ y : B0579.Plane, coef (s, (y.1 + c, y.2)) = coef (s, y)) (z : B0579.Plane) :
    qPeriodize c (fun x => coef x * β x) s z = coef (s, z) * qPeriodize c β s z := by
  have hk_per : ∀ (k : ℤ) (y : B0579.Plane), coef (s, (y.1 + (k : ℝ) * c, y.2)) = coef (s, y) := by
    intro k
    induction k using Int.induction_on with
    | zero => intro y; simp
    | succ n ih =>
      intro y
      push_cast at ih ⊢
      have heq : y.1 + ((n : ℝ) + 1) * c = (y.1 + (n : ℝ) * c) + c := by ring
      rw [heq, hper (y.1 + (n : ℝ) * c, y.2), ih y]
    | pred n ih =>
      intro y
      push_cast at ih ⊢
      have heq : (y.1 + (-(n : ℝ) - 1) * c) + c = y.1 + -(n : ℝ) * c := by ring
      have h1 := hper (y.1 + (-(n : ℝ) - 1) * c, y.2)
      dsimp at h1
      rw [heq] at h1
      rw [← h1, ih y]
  unfold qPeriodize
  simp_rw [hk_per _ z]
  exact tsum_mul_left

private theorem cpd_neg_fun (α : Coord → ℝ) (j : Fin 3) :
    cpd j (fun x => -α x) = fun x => -cpd j α x := by
  funext x
  unfold cpd
  rw [fderiv_fun_neg]
  simp

private theorem pd_comm_plane {f : B0579.Plane → ℝ} (hf : ContDiff ℝ ∞ f) (j k : Fin 2) :
    B0579.pd j (B0579.pd k f) = B0579.pd k (B0579.pd j f) := by
  funext x
  have hs : IsSymmSndFDerivAt ℝ f x := hf.contDiffAt.isSymmSndFDerivAt (by simp)
  have hdf : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (m := ∞) (by simp)
  have key : ∀ a b : Fin 2,
      B0579.pd b (B0579.pd a f) x = fderiv ℝ (fderiv ℝ f) x (B0579.dir b) (B0579.dir a) := by
    intro a b
    unfold B0579.pd
    have hd : DifferentiableAt ℝ (fderiv ℝ f) x := (hdf.differentiable (by simp)).differentiableAt
    rw [fderiv_clm_apply hd (differentiableAt_const _)]
    simp
  rw [key, key]
  exact hs _ _

private theorem pd_add_fun {f g : B0579.Plane → ℝ} (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) (j : Fin 2) :
    B0579.pd j (fun y => f y + g y) = fun y => B0579.pd j f y + B0579.pd j g y := by
  funext x
  unfold B0579.pd
  rw [fderiv_fun_add (hf x) (hg x)]
  simp

private theorem pd_neg_fun (f : B0579.Plane → ℝ) (j : Fin 2) :
    B0579.pd j (fun y => -f y) = fun y => -B0579.pd j f y := by
  funext x
  unfold B0579.pd
  rw [fderiv_fun_neg]
  simp

private theorem pd_mul_at {f g : B0579.Plane → ℝ} (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) (j : Fin 2) (x : B0579.Plane) :
    B0579.pd j (fun y => f y * g y) x = B0579.pd j f x * g x + f x * B0579.pd j g x := by
  unfold B0579.pd
  rw [fderiv_fun_mul (hf x) (hg x)]
  simp
  ring

private def SmPer (c : ℝ) (a : B0579.Plane → ℝ) : Prop :=
  ContDiff ℝ ∞ a ∧ ∀ x : B0579.Plane, a (x.1 + c, x.2) = a x

private theorem SmPer.pd {c : ℝ} {a : B0579.Plane → ℝ} (ha : SmPer c a) (j : Fin 2) :
    SmPer c (B0579.pd j a) := by
  refine ⟨((contDiff_infty_iff_fderiv.1 ha.1).2).clm_apply contDiff_const, fun x => ?_⟩
  have hfun : (fun y : B0579.Plane => a (y + ((c, 0) : B0579.Plane))) = a := by
    funext y
    have hy : y + ((c, 0) : B0579.Plane) = (y.1 + c, y.2) := by ext <;> simp
    rw [hy]
    exact ha.2 y
  have h := fderiv_comp_add_right (𝕜 := ℝ) (f := a) (x := x) ((c, 0) : B0579.Plane)
  rw [hfun] at h
  have hx : x + ((c, 0) : B0579.Plane) = (x.1 + c, x.2) := by ext <;> simp
  rw [hx] at h
  simp only [B0579.pd]
  rw [← h]

private theorem SmPer.sub {c : ℝ} {a b : B0579.Plane → ℝ} (ha : SmPer c a) (hb : SmPer c b) :
    SmPer c (fun x => a x - b x) :=
  ⟨ha.1.sub hb.1, fun x => by simp [ha.2 x, hb.2 x]⟩

private theorem isCylTest_add {c : ℝ} {f g : B0579.Plane → ℝ}
    (hf : B0579.IsCylTest c f) (hg : B0579.IsCylTest c g) :
    B0579.IsCylTest c (fun x => f x + g x) where
  smooth := hf.smooth.add hg.smooth
  periodic x := by simp [hf.periodic x, hg.periodic x]
  band := by
    obtain ⟨R1, h1⟩ := hf.band
    obtain ⟨R2, h2⟩ := hg.band
    refine ⟨max R1 R2, fun x hx => ?_⟩
    rw [h1 x ((le_max_left _ _).trans_lt hx), h2 x ((le_max_right _ _).trans_lt hx), add_zero]

private theorem isCylTest_neg {c : ℝ} {f : B0579.Plane → ℝ} (hf : B0579.IsCylTest c f) :
    B0579.IsCylTest c (fun x => -f x) where
  smooth := hf.smooth.neg
  periodic x := by simp [hf.periodic x]
  band := by
    obtain ⟨R, hR⟩ := hf.band
    exact ⟨R, fun x hx => by simp [hR x hx]⟩

private theorem isCylTest_mul_smper {c : ℝ} {a χ : B0579.Plane → ℝ}
    (ha : SmPer c a) (hχ : B0579.IsCylTest c χ) :
    B0579.IsCylTest c (fun x => a x * χ x) where
  smooth := ha.1.mul hχ.smooth
  periodic x := by simp [ha.2 x, hχ.periodic x]
  band := by
    obtain ⟨R, hR⟩ := hχ.band
    exact ⟨R, fun x hx => by simp [hR x hx]⟩

private theorem train_v_smper {ν c : ℝ} (tr : B0140.TrainSol ν c) {s : ℝ} (hs : 0 < s)
    (i : Fin 2) : SmPer c (fun x => tr.v s x i) :=
  ⟨(EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp (B0238.contDiff_Vc tr hs.le),
    fun x => by
      show (tr.v s (x.1 + c, x.2)) i = (tr.v s x) i
      rw [tr.isTrain.periodic_v s hs.le x]⟩

private theorem train_Ec_eq {ν c : ℝ} (tr : B0140.TrainSol ν c) {s : ℝ} (hs : 0 < s) :
    B0238.Ec tr s = fun z =>
      B0579.pd 0 (fun w => tr.v s w 1) z - B0579.pd 1 (fun w => tr.v s w 0) z := by
  funext z
  exact B0238.curl_eq_fderiv ((B0238.contDiff_Vc tr hs.le).of_le (by simp)) z

private theorem train_Ec_smper {ν c : ℝ} (tr : B0140.TrainSol ν c) {s : ℝ} (hs : 0 < s) :
    SmPer c (B0238.Ec tr s) := by
  rw [train_Ec_eq tr hs]
  exact ((train_v_smper tr hs 1).pd 0).sub ((train_v_smper tr hs 0).pd 1)

private theorem integrableOn_memLp_mul_cylTest {c : ℝ} {u : B0579.Plane → ℂ}
    (hu : MemLp u 2 (volume.restrict (B0579.cell c))) {ψ : B0579.Plane → ℝ}
    (hψ : B0579.IsCylTest c ψ) :
    IntegrableOn (fun y => u y * (ψ y : ℂ)) (B0579.cell c) volume := by
  obtain ⟨R, hR⟩ := hψ.vanish
  have h2 : MemLp ψ 2 (volume.restrict (B0579.cell c)) :=
    B0579.memLp_cell_of_continuous hψ.continuous (B0579.isCompact_box c R) hR
  exact hu.integrable_mul h2.ofReal

private theorem unfold_profile_coord {c a b R M : ℝ} (hc : 0 < c) (ha : 0 < a) (hab : a ≤ b)
    (hR : 0 < R) {w : CProf} (hw_sm : StronglyMeasurable w) (hw_per : QPeriodic c w)
    (hw_L2 : ∀ s ∈ Icc a b,
      eLpNorm (fun y => w (s, y)) 2 (volume.restrict (B0579.cell c)) ≤ ENNReal.ofReal M)
    (i : Fin 2) {α : Coord → ℝ} (hα_cont : Continuous α)
    (hα_supp : ∀ x : Coord, (x.1 ∉ Icc a b ∨ R < |x.2.1| ∨ R < |x.2.2|) → α x = 0) :
    Integrable (fun x : Coord => w x i * (α x : ℂ)) volume ∧
      IntegrableOn (fun x : Coord => w x i * (qPeriodize c α x.1 x.2 : ℂ))
        (Icc a b ×ˢ B0579.cell c) volume ∧
      ∫ x : Coord, w x i * (α x : ℂ) =
        ∫ s in Icc a b, ∫ y in B0579.cell c, w (s, y) i * (qPeriodize c α s y : ℂ) := by
  have hu_sm : StronglyMeasurable (fun x : Coord => w x i) :=
    (EuclideanSpace.proj (𝕜 := ℂ) i).continuous.comp_stronglyMeasurable hw_sm
  have hu_per : ∀ᵐ x ∂(volume.restrict {x : Coord | 0 < x.1}), w (qShift c x) i = w x i := by
    filter_upwards [hw_per] with x hx
    exact congr_arg (fun v => v i) hx
  have hu_loc : (∫⁻ s in Icc a b,
      eLpNorm (fun y => w (s, y) i) 2 (volume.restrict (B0579.cell c))) < ⊤ := by
    have hle : ∀ s ∈ Icc a b,
        eLpNorm (fun y => w (s, y) i) 2 (volume.restrict (B0579.cell c)) ≤ ENNReal.ofReal M := by
      intro s hs
      refine (eLpNorm_mono_enorm fun y => ?_).trans (hw_L2 s hs)
      simp only [enorm_eq_nnnorm, ENNReal.coe_le_coe, ← norm_toNNReal]
      exact Real.toNNReal_le_toNNReal (PiLp.norm_apply_le (w (s, y)) i)
    calc ∫⁻ s in Icc a b, eLpNorm (fun y => w (s, y) i) 2 (volume.restrict (B0579.cell c))
        ≤ ∫⁻ _s in Icc a b, ENNReal.ofReal M := setLIntegral_mono' measurableSet_Icc hle
      _ = ENNReal.ofReal M * volume (Icc a b) := by rw [setLIntegral_const]
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
          (by rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top)
  exact integrable_and_integral_coord_eq_cell_qPeriodize hc ha hab hR
    hu_sm.aestronglyMeasurable hu_per hu_loc hα_cont hα_supp

private theorem continuous_mul_cutoff {a b R : ℝ} (ha : 0 < a)
    {coef β : Coord → ℝ} (hcoef : ContinuousOn coef (Ioi 0 ×ˢ univ))
    (hβ_cont : Continuous β)
    (hβ_supp : ∀ x : Coord, (x.1 ∉ Icc a b ∨ R < |x.2.1| ∨ R < |x.2.2|) → β x = 0) :
    Continuous (fun x : Coord => coef x * β x) := by
  rw [continuous_iff_continuousAt]
  intro x₀
  by_cases hx₀ : 0 < x₀.1
  · have hU : Ioi (0 : ℝ) ×ˢ (univ : Set B0579.Plane) ∈ 𝓝 x₀ :=
      (isOpen_Ioi.prod isOpen_univ).mem_nhds ⟨hx₀, trivial⟩
    exact (hcoef.mul hβ_cont.continuousOn).continuousAt hU
  · have hx_lt : x₀.1 < a := lt_of_le_of_lt (not_lt.1 hx₀) ha
    have hV : {x : Coord | x.1 < a} ∈ 𝓝 x₀ :=
      (isOpen_lt continuous_fst continuous_const).mem_nhds hx_lt
    have hev : (fun x : Coord => coef x * β x) =ᶠ[𝓝 x₀] fun _ => (0 : ℝ) := by
      filter_upwards [hV] with x (hx : x.1 < a)
      have h0 : β x = 0 := hβ_supp x (Or.inl fun h => absurd h.1 (not_le.2 hx))
      rw [h0, mul_zero]
    exact continuousAt_const.congr hev.symm

private theorem continuousOn_train_pd_pos {ν c : ℝ} (tr : B0140.TrainSol ν c)
    (k i : Fin 2) :
    ContinuousOn (fun x : Coord => B0579.pd k (fun y => tr.v x.1 y i) x.2)
      (Ioi 0 ×ˢ univ) := by
  let U : Set Coord := Ioi 0 ×ˢ univ
  have hU_open : IsOpen U := isOpen_Ioi.prod isOpen_univ
  have hsm_v : ContDiffOn ℝ ∞ (fun x : Coord => tr.v x.1 x.2) U :=
    tr.isTrain.smooth_v.mono (prod_mono Ioi_subset_Ici_self Subset.rfl)
  have hsm_i : ContDiffOn ℝ ∞ (UnforcedLeray.Short.PartI.crFc tr.v i) U :=
    UnforcedLeray.Short.PartI.crFc_contDiffOn hsm_v i
  have hcont_fd : ContinuousOn
      (fun x : Coord => fderiv ℝ (UnforcedLeray.Short.PartI.crFc tr.v i) x (0, B0579.dir k)) U :=
    (hsm_i.continuousOn_fderiv_of_isOpen hU_open (by simp)).clm_apply continuousOn_const
  refine hcont_fd.congr ?_
  intro ⟨s, z⟩ hsz
  have hd_joint : HasFDerivAt (UnforcedLeray.Short.PartI.crFc tr.v i)
      (fderiv ℝ (UnforcedLeray.Short.PartI.crFc tr.v i) (s, z)) (s, z) :=
    ((hsm_i.contDiffAt (hU_open.mem_nhds hsz)).differentiableAt (by simp)).hasFDerivAt
  have hι : HasFDerivAt (fun y : B0579.Plane => ((s, y) : Coord))
      ((0 : B0579.Plane →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ B0579.Plane)) z :=
    (hasFDerivAt_const s z).prodMk (hasFDerivAt_id z)
  dsimp
  change fderiv ℝ ((UnforcedLeray.Short.PartI.crFc tr.v i) ∘ fun y => ((s, y) : Coord)) z
      (B0579.dir k) = _
  rw [(hd_joint.comp z hι).fderiv]
  simp

private theorem setIntegral_prod_vol {f : Coord → ℂ} {s : Set ℝ} {t : Set B0579.Plane}
    (hf : IntegrableOn f (s ×ˢ t) volume) :
    ∫ z in s ×ˢ t, f z = ∫ x in s, ∫ y in t, f (x, y) :=
  setIntegral_prod f hf

private theorem integrableOn_and_setIntegral_prod_eq {f : Coord → ℂ} {g : ℝ → ℂ}
    {s : Set ℝ} {t : Set B0579.Plane} (hs : MeasurableSet s)
    (hf : IntegrableOn f (s ×ˢ t) volume)
    (hfg : ∀ x ∈ s, (∫ y in t, f (x, y)) = g x) :
    IntegrableOn g s volume ∧ (∫ z in s ×ˢ t, f z) = ∫ x in s, g x := by
  have hvol : (volume : Measure Coord) = volume.prod volume := Measure.volume_eq_prod ℝ B0579.Plane
  rw [hvol] at hf ⊢
  have hf' : Integrable f ((volume.restrict s).prod (volume.restrict t)) := by
    rwa [Measure.prod_restrict]
  have hint : IntegrableOn (fun x => ∫ y in t, f (x, y)) s volume := hf'.integral_prod_left
  refine ⟨hint.congr_fun hfg hs, ?_⟩
  rw [setIntegral_prod _ hf]
  exact setIntegral_congr_fun hs hfg

private theorem isCoordTest_cpd {α : Coord → ℝ} (hα : IsCoordTest α) (j : Fin 3) :
    IsCoordTest (cpd j α) :=
  planarTest_isCoordTest_partial hα (cdir j)

private theorem qPeriodize_cpd1 {c : ℝ} (hc : 0 < c) {α : Coord → ℝ}
    (hα : IsCoordTest α) (s : ℝ) :
    qPeriodize c (cpd 1 α) s = B0579.pd 0 (qPeriodize c α s) :=
  funext fun y => (pd_qPeriodize hc hα s 0 y).symm

private theorem qPeriodize_cpd2 {c : ℝ} (hc : 0 < c) {α : Coord → ℝ}
    (hα : IsCoordTest α) (s : ℝ) :
    qPeriodize c (cpd 2 α) s = B0579.pd 1 (qPeriodize c α s) :=
  funext fun y => (pd_qPeriodize hc hα s 1 y).symm

private theorem coord_meridTranspose_eq {m : ℝ} {p : Params} (hc1 : 1 ≤ p.c) (_hH : 0 < p.H)
    {om : ℝ → Xmc p.c m}
    {z zq zη : CProf} (hz_sm : StronglyMeasurable z) (hz_per : QPeriodic p.c z)
    (hz_H1 : ∃ M : ℝ, ∀ s ∈ Ioc 0 p.H, sliceH1Norm p.c z zq zη s ≤ ENNReal.ofReal M)
    (hz_slice : ∀ s ∈ Ioc 0 p.H,
      IIIa.IsBiotSavart p.c (fun x => ((om s x : ℝ) : ℂ)) (fun x j => z (s, x) j) ∧
      (∀ j : Fin 2,
        IIIa.HasWeakCellDerivC p.c 0 (fun x => z (s, x) j) (fun x => zq (s, x) j) ∧
        IIIa.HasWeakCellDerivC p.c 1 (fun x => z (s, x) j) (fun x => zη (s, x) j)) ∧
      (fun x (j : Fin 2) => ((UnforcedLeray.Cyl.K p.c (om s) x j : ℝ) : ℂ)) =ᵐ[
          volume.restrict (B0579.cell p.c)]
        (fun x j => z (s, x) j))
    {Ψ : Coord → Fin 2 → ℝ} (hΨ : IsPlanarSolTest Ψ)
    {Φ : Coord → ℝ} {a b R : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbH : b < p.H) (hR : 0 < R)
    (hΦ_test : IsCoordTest Φ)
    (hΦ_box : tsupport Φ ⊆ Icc a b ×ˢ (Icc (-R) R ×ˢ Icc (-R) R))
    (hΨ_Φ : ∀ x : Coord, Ψ x 0 = cpd 2 Φ x ∧ Ψ x 1 = -cpd 1 Φ x) :
    let φ := qPeriodize p.c Φ
    let φ_s := qPeriodize p.c (cpd 0 Φ)
    Integrable (fun x => ∑ i : Fin 2, z x i * meridTranspose p.ν Ψ x i) volume ∧
      IntegrableOn
        (fun s =>
          (-(((∫ y in B0579.cell p.c, om s y * φ_s s y : ℝ) : ℂ)) -
            (((∫ y in B0579.cell p.c, om s y * (p.ν * IIIa.lapP (φ s) y) : ℝ) : ℂ))))
        (Icc a b) volume ∧
      ∫ x, ∑ i : Fin 2, z x i * meridTranspose p.ν Ψ x i =
        ∫ s in Icc a b,
          (-(((∫ y in B0579.cell p.c, om s y * φ_s s y : ℝ) : ℂ)) -
            (((∫ y in B0579.cell p.c, om s y * (p.ν * IIIa.lapP (φ s) y) : ℝ) : ℂ))) := by
  intro φ φ_s
  have hc0 : 0 < p.c := by linarith
  obtain ⟨M, hM⟩ := hz_H1
  have hz_L2 : ∀ s ∈ Icc a b,
      eLpNorm (fun y => z (s, y)) 2 (volume.restrict (B0579.cell p.c)) ≤ ENNReal.ofReal M := by
    intro s hs
    have hs_Ioc : s ∈ Ioc 0 p.H := ⟨lt_of_lt_of_le ha hs.1, hs.2.trans hbH.le⟩
    exact (le_add_of_nonneg_right zero_le).trans
      ((le_add_of_nonneg_right zero_le).trans (hM s hs_Ioc))
  let Box : Set Coord := Icc a b ×ˢ (Icc (-R) R ×ˢ Icc (-R) R)
  let mtR : Fin 2 → Coord → ℝ := fun i x =>
    -cpd 0 (fun y => Ψ y i) x -
      p.ν * (cpd 1 (cpd 1 (fun y => Ψ y i)) x + cpd 2 (cpd 2 (fun y => Ψ y i)) x)
  have hmt_cast : ∀ (i : Fin 2) (x : Coord), (mtR i x : ℂ) = meridTranspose p.ν Ψ x i := by
    intro i x; dsimp [mtR, meridTranspose]; push_cast; rfl
  have hΨ_box : ∀ i : Fin 2, tsupport (fun y => Ψ y i) ⊆ Box := by
    intro i
    fin_cases i
    · change tsupport (fun y => Ψ y 0) ⊆ Box
      have heq : (fun y => Ψ y 0) = cpd 2 Φ := funext fun x => (hΨ_Φ x).1
      rw [heq]; exact (tsupport_cpd_subset 2).trans hΦ_box
    · change tsupport (fun y => Ψ y 1) ⊆ Box
      have heq : (fun y => Ψ y 1) = -cpd 1 Φ := funext fun x => (hΨ_Φ x).2
      rw [heq, tsupport_neg]; exact (tsupport_cpd_subset 1).trans hΦ_box
  have hmt_cont : ∀ i : Fin 2, Continuous (mtR i) := by
    intro i
    have h0 := (planarTest_isCoordTest_partial (hΨ.smooth i) (cdir 0)).smooth.continuous
    have h1 := (planarTest_isCoordTest_partial
      (planarTest_isCoordTest_partial (hΨ.smooth i) (cdir 1)) (cdir 1)).smooth.continuous
    have h2 := (planarTest_isCoordTest_partial
      (planarTest_isCoordTest_partial (hΨ.smooth i) (cdir 2)) (cdir 2)).smooth.continuous
    exact h0.neg.sub (continuous_const.mul (h1.add h2))
  have hmt_supp : ∀ (i : Fin 2) (x : Coord),
      (x.1 ∉ Icc a b ∨ R < |x.2.1| ∨ R < |x.2.2|) → mtR i x = 0 := by
    intro i x hx
    have tb0 : tsupport (cpd 0 (fun y => Ψ y i)) ⊆ Box :=
      (tsupport_cpd_subset 0).trans (hΨ_box i)
    have tb11 : tsupport (cpd 1 (cpd 1 (fun y => Ψ y i))) ⊆ Box :=
      (tsupport_cpd_subset 1).trans ((tsupport_cpd_subset 1).trans (hΨ_box i))
    have tb22 : tsupport (cpd 2 (cpd 2 (fun y => Ψ y i))) ⊆ Box :=
      (tsupport_cpd_subset 2).trans ((tsupport_cpd_subset 2).trans (hΨ_box i))
    dsimp [mtR]
    rw [notMem_box_vanish tb0 x hx, notMem_box_vanish tb11 x hx, notMem_box_vanish tb22 x hx]
    ring
  obtain ⟨hi0, hip0, heq0⟩ :=
    unfold_profile_coord hc0 ha hab hR hz_sm hz_per hz_L2 0 (hmt_cont 0) (hmt_supp 0)
  obtain ⟨hi1, hip1, heq1⟩ :=
    unfold_profile_coord hc0 ha hab hR hz_sm hz_per hz_L2 1 (hmt_cont 1) (hmt_supp 1)
  have hsum_fun : (fun x : Coord => ∑ i : Fin 2, z x i * meridTranspose p.ν Ψ x i) =
      fun x : Coord => z x 0 * (mtR 0 x : ℂ) + z x 1 * (mtR 1 x : ℂ) := by
    funext x
    rw [Fin.sum_univ_two, hmt_cast 0 x, hmt_cast 1 x]
  rw [hsum_fun]
  refine ⟨int_add hi0 hi1, ?_⟩
  rw [integral_add hi0 hi1, heq0, heq1,
    ← setIntegral_prod_vol hip0, ← setIntegral_prod_vol hip1,
    ← integral_add hip0 hip1]
  refine integrableOn_and_setIntegral_prod_eq measurableSet_Icc (intOn_add hip0 hip1) fun s hs => ?_
  dsimp only
  have hs_Ioc : s ∈ Ioc 0 p.H := ⟨lt_of_lt_of_le ha hs.1, hs.2.trans hbH.le⟩
  have hΦ0_test : IsCoordTest (cpd 0 Φ) := isCoordTest_cpd hΦ_test 0
  have hζ : B0579.IsCylTest p.c (φ s) := isCylTest_qPeriodize hc0 hΦ_test s
  have hζ_s : B0579.IsCylTest p.c (φ_s s) := isCylTest_qPeriodize hc0 hΦ0_test s
  have hlap_cyl : B0579.IsCylTest p.c (IIIa.lapP (φ s)) :=
    isCylTest_add ((hζ.pd 0).pd 0) ((hζ.pd 1).pd 1)
  -- Express qPeriodize (mtR 0) s and qPeriodize (mtR 1) s in terms of φ s and φ_s s
  have hqP_Ψ0 : qPeriodize p.c (fun y => Ψ y 0) s = B0579.pd 1 (φ s) := by
    have heq : (fun w => Ψ w 0) = cpd 2 Φ := funext fun w => (hΨ_Φ w).1
    rw [heq]; exact qPeriodize_cpd2 hc0 hΦ_test s
  have hqP_Ψ1 : qPeriodize p.c (fun y => Ψ y 1) s = fun y => -B0579.pd 0 (φ s) y := by
    funext y
    have heq : (fun w => Ψ w 1) = fun w => -cpd 1 Φ w := funext fun w => (hΨ_Φ w).2
    rw [heq, qPeriodize_neg, qPeriodize_cpd1 hc0 hΦ_test s]
  have hvan_q : ∀ {α : Coord → ℝ}, tsupport α ⊆ Box → ∀ x : Coord, R < |x.2.1| → α x = 0 :=
    fun htb x hx => notMem_box_vanish htb x (Or.inr (Or.inl hx))
  have hmt0_qP : ∀ y : B0579.Plane,
      qPeriodize p.c (mtR 0) s y =
        -B0579.pd 1 (φ_s s) y - p.ν * B0579.pd 1 (IIIa.lapP (φ s)) y := by
    intro y
    have tb0 : tsupport (cpd 0 (fun w => Ψ w 0)) ⊆ Box :=
      (tsupport_cpd_subset 0).trans (hΨ_box 0)
    have tb11 : tsupport (cpd 1 (cpd 1 (fun w => Ψ w 0))) ⊆ Box :=
      (tsupport_cpd_subset 1).trans ((tsupport_cpd_subset 1).trans (hΨ_box 0))
    have tb22 : tsupport (cpd 2 (cpd 2 (fun w => Ψ w 0))) ⊆ Box :=
      (tsupport_cpd_subset 2).trans ((tsupport_cpd_subset 2).trans (hΨ_box 0))
    have hvan_lap : ∀ x : Coord, R < |x.2.1| →
        p.ν * (cpd 1 (cpd 1 (fun w => Ψ w 0)) x + cpd 2 (cpd 2 (fun w => Ψ w 0)) x) = 0 := by
      intro x hx; rw [hvan_q tb11 x hx, hvan_q tb22 x hx]; ring
    dsimp [mtR]
    rw [qPeriodize_sub hc0 (fun x hx => by rw [hvan_q tb0 x hx, neg_zero]) hvan_lap,
      qPeriodize_neg, qPeriodize_const_mul,
      qPeriodize_add hc0 (hvan_q tb11) (hvan_q tb22)]
    have hc0_eq : cpd 0 (fun w => Ψ w 0) = cpd 2 (cpd 0 Φ) := by
      have heq : (fun w => Ψ w 0) = cpd 2 Φ := funext fun w => (hΨ_Φ w).1
      rw [heq]; exact cpd_comm hΦ_test.smooth 0 2
    have h11_eq : qPeriodize p.c (cpd 1 (cpd 1 (fun w => Ψ w 0))) s y =
        B0579.pd 0 (B0579.pd 0 (B0579.pd 1 (φ s))) y := by
      rw [qPeriodize_cpd1 hc0 (isCoordTest_cpd (hΨ.smooth 0) 1) s,
        qPeriodize_cpd1 hc0 (hΨ.smooth 0) s, hqP_Ψ0]
    have h22_eq : qPeriodize p.c (cpd 2 (cpd 2 (fun w => Ψ w 0))) s y =
        B0579.pd 1 (B0579.pd 1 (B0579.pd 1 (φ s))) y := by
      rw [qPeriodize_cpd2 hc0 (isCoordTest_cpd (hΨ.smooth 0) 2) s,
        qPeriodize_cpd2 hc0 (hΨ.smooth 0) s, hqP_Ψ0]
    have hcomm_lap : B0579.pd 1 (IIIa.lapP (φ s)) y =
        B0579.pd 0 (B0579.pd 0 (B0579.pd 1 (φ s))) y +
          B0579.pd 1 (B0579.pd 1 (B0579.pd 1 (φ s))) y := by
      unfold IIIa.lapP
      have ha_diff := ((hζ.pd 0).pd 0).differentiable
      have hb_diff := ((hζ.pd 1).pd 1).differentiable
      have hadd := congr_fun (pd_add_fun ha_diff hb_diff 1) y
      rw [hadd]
      have hc1 := pd_comm_plane (hζ.pd 0).smooth 1 0
      have hc2 := pd_comm_plane hζ.smooth 1 0
      rw [hc1, hc2]
    rw [hc0_eq, qPeriodize_cpd2 hc0 hΦ0_test s, h11_eq, h22_eq, ← hcomm_lap]
  have hmt1_qP : ∀ y : B0579.Plane,
      qPeriodize p.c (mtR 1) s y =
        B0579.pd 0 (φ_s s) y + p.ν * B0579.pd 0 (IIIa.lapP (φ s)) y := by
    intro y
    have tb0 : tsupport (cpd 0 (fun w => Ψ w 1)) ⊆ Box :=
      (tsupport_cpd_subset 0).trans (hΨ_box 1)
    have tb11 : tsupport (cpd 1 (cpd 1 (fun w => Ψ w 1))) ⊆ Box :=
      (tsupport_cpd_subset 1).trans ((tsupport_cpd_subset 1).trans (hΨ_box 1))
    have tb22 : tsupport (cpd 2 (cpd 2 (fun w => Ψ w 1))) ⊆ Box :=
      (tsupport_cpd_subset 2).trans ((tsupport_cpd_subset 2).trans (hΨ_box 1))
    have hvan_lap : ∀ x : Coord, R < |x.2.1| →
        p.ν * (cpd 1 (cpd 1 (fun w => Ψ w 1)) x + cpd 2 (cpd 2 (fun w => Ψ w 1)) x) = 0 := by
      intro x hx; rw [hvan_q tb11 x hx, hvan_q tb22 x hx]; ring
    dsimp [mtR]
    rw [qPeriodize_sub hc0 (fun x hx => by rw [hvan_q tb0 x hx, neg_zero]) hvan_lap,
      qPeriodize_neg, qPeriodize_const_mul,
      qPeriodize_add hc0 (hvan_q tb11) (hvan_q tb22)]
    have hc0_eq : cpd 0 (fun w => Ψ w 1) = fun w => -cpd 1 (cpd 0 Φ) w := by
      have heq : (fun w => Ψ w 1) = fun w => -cpd 1 Φ w := funext fun w => (hΨ_Φ w).2
      rw [heq, cpd_neg_fun, cpd_comm hΦ_test.smooth 0 1]
    have h11_eq : qPeriodize p.c (cpd 1 (cpd 1 (fun w => Ψ w 1))) s y =
        -B0579.pd 0 (B0579.pd 0 (B0579.pd 0 (φ s))) y := by
      rw [qPeriodize_cpd1 hc0 (isCoordTest_cpd (hΨ.smooth 1) 1) s,
        qPeriodize_cpd1 hc0 (hΨ.smooth 1) s, hqP_Ψ1, pd_neg_fun, pd_neg_fun]
    have h22_eq : qPeriodize p.c (cpd 2 (cpd 2 (fun w => Ψ w 1))) s y =
        -B0579.pd 1 (B0579.pd 1 (B0579.pd 0 (φ s))) y := by
      rw [qPeriodize_cpd2 hc0 (isCoordTest_cpd (hΨ.smooth 1) 2) s,
        qPeriodize_cpd2 hc0 (hΨ.smooth 1) s, hqP_Ψ1, pd_neg_fun, pd_neg_fun]
    have hcomm_lap : B0579.pd 0 (IIIa.lapP (φ s)) y =
        B0579.pd 0 (B0579.pd 0 (B0579.pd 0 (φ s))) y +
          B0579.pd 1 (B0579.pd 1 (B0579.pd 0 (φ s))) y := by
      unfold IIIa.lapP
      have ha_diff := ((hζ.pd 0).pd 0).differentiable
      have hb_diff := ((hζ.pd 1).pd 1).differentiable
      have hadd := congr_fun (pd_add_fun ha_diff hb_diff 0) y
      rw [hadd]
      have hc1 := pd_comm_plane (hζ.pd 1).smooth 0 1
      have hc2 := pd_comm_plane hζ.smooth 0 1
      rw [hc1, hc2]
    rw [hc0_eq, qPeriodize_neg, qPeriodize_cpd1 hc0 hΦ0_test s, h11_eq, h22_eq]
    change - -B0579.pd 0 (φ_s s) y -
        p.ν * (-B0579.pd 0 (B0579.pd 0 (B0579.pd 0 (φ s))) y +
          -B0579.pd 1 (B0579.pd 1 (B0579.pd 0 (φ s))) y) =
      B0579.pd 0 (φ_s s) y + p.ν * B0579.pd 0 (IIIa.lapP (φ s)) y
    rw [hcomm_lap]; ring
  -- Apply IsBiotSavart on B0579.cell p.c
  have hbs := (hz_slice s hs_Ioc).1
  have hz0_mem : MemLp (fun y => z (s, y) 0) 2 (volume.restrict (B0579.cell p.c)) := hbs.1 0
  have hz1_mem : MemLp (fun y => z (s, y) 1) 2 (volume.restrict (B0579.cell p.c)) := hbs.1 1
  have i_s0 := integrableOn_memLp_mul_cylTest hz0_mem (hζ_s.pd 1)
  have i_s1 := integrableOn_memLp_mul_cylTest hz1_mem (hζ_s.pd 0)
  have i_l0 := integrableOn_memLp_mul_cylTest hz0_mem (hlap_cyl.pd 1)
  have i_l1 := integrableOn_memLp_mul_cylTest hz1_mem (hlap_cyl.pd 0)
  have hpt : ∀ y : B0579.Plane,
      z (s, y) 0 * (qPeriodize p.c (mtR 0) s y : ℂ) +
        z (s, y) 1 * (qPeriodize p.c (mtR 1) s y : ℂ) =
      -(z (s, y) 0 * (B0579.pd 1 (φ_s s) y : ℂ) - z (s, y) 1 * (B0579.pd 0 (φ_s s) y : ℂ)) -
        (p.ν : ℂ) * (z (s, y) 0 * (B0579.pd 1 (IIIa.lapP (φ s)) y : ℂ) -
          z (s, y) 1 * (B0579.pd 0 (IIIa.lapP (φ s)) y : ℂ)) := by
    intro y
    rw [hmt0_qP y, hmt1_qP y]
    push_cast
    ring
  simp_rw [hpt]
  rw [integral_sub (intOn_neg (intOn_sub i_s0 i_s1)) ((intOn_sub i_l0 i_l1).const_mul (p.ν : ℂ)),
    integral_neg, integral_const_mul,
    ← hbs.2.2 (φ_s s) hζ_s, ← hbs.2.2 (IIIa.lapP (φ s)) hlap_cyl]
  have hcast1 : (∫ y in B0579.cell p.c, ((om s y : ℝ) : ℂ) * (φ_s s y : ℂ)) =
      ((∫ y in B0579.cell p.c, om s y * φ_s s y : ℝ) : ℂ) := by
    simp_rw [← Complex.ofReal_mul]
    exact integral_ofReal
  have hcast2 : (p.ν : ℂ) * (∫ y in B0579.cell p.c, ((om s y : ℝ) : ℂ) * (IIIa.lapP (φ s) y : ℂ)) =
      ((∫ y in B0579.cell p.c, om s y * (p.ν * IIIa.lapP (φ s) y) : ℝ) : ℂ) := by
    simp_rw [← Complex.ofReal_mul]
    rw [show (∫ y in B0579.cell p.c, ((om s y * IIIa.lapP (φ s) y : ℝ) : ℂ)) =
          ((∫ y in B0579.cell p.c, om s y * IIIa.lapP (φ s) y : ℝ) : ℂ) from integral_ofReal,
      ← Complex.ofReal_mul]
    congr 1
    rw [← integral_const_mul]
    congr 1; funext y; ring
  rw [hcast1, hcast2]

private theorem coord_flatBv_eq {m : ℝ} {p : Params} (hc1 : 1 ≤ p.c) (_hH : 0 < p.H)
    {om : ℝ → Xmc p.c m}
    {z zq zη : CProf}
    (hz_sm : StronglyMeasurable z) (hzq_sm : StronglyMeasurable zq) (hzη_sm : StronglyMeasurable zη)
    (hz_per : QPeriodic p.c z) (hzq_per : QPeriodic p.c zq) (hzη_per : QPeriodic p.c zη)
    (hz_H1 : ∃ M : ℝ, ∀ s ∈ Ioc 0 p.H, sliceH1Norm p.c z zq zη s ≤ ENNReal.ofReal M)
    (hz_slice : ∀ s ∈ Ioc 0 p.H,
      IIIa.IsBiotSavart p.c (fun x => ((om s x : ℝ) : ℂ)) (fun x j => z (s, x) j) ∧
      (∀ j : Fin 2,
        IIIa.HasWeakCellDerivC p.c 0 (fun x => z (s, x) j) (fun x => zq (s, x) j) ∧
        IIIa.HasWeakCellDerivC p.c 1 (fun x => z (s, x) j) (fun x => zη (s, x) j)) ∧
      (fun x (j : Fin 2) => ((UnforcedLeray.Cyl.K p.c (om s) x j : ℝ) : ℂ)) =ᵐ[
          volume.restrict (B0579.cell p.c)]
        (fun x j => z (s, x) j))
    {Ψ : Coord → Fin 2 → ℝ} (hΨ : IsPlanarSolTest Ψ)
    {Φ : Coord → ℝ} {a b R : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbH : b < p.H) (hR : 0 < R)
    (hΦ_test : IsCoordTest Φ)
    (hΦ_box : tsupport Φ ⊆ Icc a b ×ˢ (Icc (-R) R ×ˢ Icc (-R) R))
    (hΨ_Φ : ∀ x : Coord, Ψ x 0 = cpd 2 Φ x ∧ Ψ x 1 = -cpd 1 Φ x) :
    let φ := qPeriodize p.c Φ
    Integrable (cdot (flatBv p.train z zq zη) Ψ) volume ∧
      IntegrableOn
        (fun s =>
          ((-∫ y in B0579.cell p.c,
              ((om s y : ℝ) : ℂ) *
                ((p.train.v s y 0 * B0579.pd 0 (φ s) y +
                  p.train.v s y 1 * B0579.pd 1 (φ s) y : ℝ) : ℂ)) +
            (((∫ y in B0579.cell p.c,
              (Cyl.K p.c (om s) y 0 * (φ s y * B0579.pd 0 (B0238.Ec p.train s) y) +
                Cyl.K p.c (om s) y 1 * (φ s y * B0579.pd 1 (B0238.Ec p.train s) y)) : ℝ) : ℂ))))
        (Icc a b) volume ∧
      ∫ x, cdot (flatBv p.train z zq zη) Ψ x =
        ∫ s in Icc a b,
          ((-∫ y in B0579.cell p.c,
              ((om s y : ℝ) : ℂ) *
                ((p.train.v s y 0 * B0579.pd 0 (φ s) y +
                  p.train.v s y 1 * B0579.pd 1 (φ s) y : ℝ) : ℂ)) +
            (((∫ y in B0579.cell p.c,
              (Cyl.K p.c (om s) y 0 * (φ s y * B0579.pd 0 (B0238.Ec p.train s) y) +
                Cyl.K p.c (om s) y 1 * (φ s y * B0579.pd 1 (B0238.Ec p.train s) y)) : ℝ) : ℂ))) := by
  intro φ
  have hc0 : 0 < p.c := by linarith
  obtain ⟨M, hM⟩ := hz_H1
  have hz_L2 : ∀ s ∈ Icc a b,
      eLpNorm (fun y => z (s, y)) 2 (volume.restrict (B0579.cell p.c)) ≤ ENNReal.ofReal M := by
    intro s hs
    have hs_Ioc : s ∈ Ioc 0 p.H := ⟨lt_of_lt_of_le ha hs.1, hs.2.trans hbH.le⟩
    exact (le_add_of_nonneg_right zero_le).trans
      ((le_add_of_nonneg_right zero_le).trans (hM s hs_Ioc))
  have hzq_L2 : ∀ s ∈ Icc a b,
      eLpNorm (fun y => zq (s, y)) 2 (volume.restrict (B0579.cell p.c)) ≤ ENNReal.ofReal M := by
    intro s hs
    have hs_Ioc : s ∈ Ioc 0 p.H := ⟨lt_of_lt_of_le ha hs.1, hs.2.trans hbH.le⟩
    exact (le_add_of_nonneg_left zero_le).trans
      ((le_add_of_nonneg_right zero_le).trans (hM s hs_Ioc))
  have hzη_L2 : ∀ s ∈ Icc a b,
      eLpNorm (fun y => zη (s, y)) 2 (volume.restrict (B0579.cell p.c)) ≤ ENNReal.ofReal M := by
    intro s hs
    have hs_Ioc : s ∈ Ioc 0 p.H := ⟨lt_of_lt_of_le ha hs.1, hs.2.trans hbH.le⟩
    exact (le_add_of_nonneg_left zero_le).trans (hM s hs_Ioc)
  let Box : Set Coord := Icc a b ×ˢ (Icc (-R) R ×ˢ Icc (-R) R)
  have hΨ_box : ∀ i : Fin 2, tsupport (fun y => Ψ y i) ⊆ Box := by
    intro i
    fin_cases i
    · change tsupport (fun y => Ψ y 0) ⊆ Box
      have heq : (fun y => Ψ y 0) = cpd 2 Φ := funext fun x => (hΨ_Φ x).1
      rw [heq]; exact (tsupport_cpd_subset 2).trans hΦ_box
    · change tsupport (fun y => Ψ y 1) ⊆ Box
      have heq : (fun y => Ψ y 1) = -cpd 1 Φ := funext fun x => (hΨ_Φ x).2
      rw [heq, tsupport_neg]; exact (tsupport_cpd_subset 1).trans hΦ_box
  have hΨ_supp : ∀ (i : Fin 2) (x : Coord),
      (x.1 ∉ Icc a b ∨ R < |x.2.1| ∨ R < |x.2.2|) → Ψ x i = 0 :=
    fun i x hx => notMem_box_vanish (hΨ_box i) x hx
  -- General helper for one (w, coef, Ψ_j) term
  have hunfold_term : ∀ {w : CProf}, StronglyMeasurable w → QPeriodic p.c w →
      (∀ s ∈ Icc a b, eLpNorm (fun y => w (s, y)) 2 (volume.restrict (B0579.cell p.c)) ≤
        ENNReal.ofReal M) →
      ∀ (i j : Fin 2) {coef : Coord → ℝ},
        ContinuousOn coef (Ioi 0 ×ˢ univ) →
        (∀ s : ℝ, 0 < s → ∀ y : B0579.Plane, coef (s, (y.1 + p.c, y.2)) = coef (s, y)) →
        Integrable (fun x : Coord => w x i * ((coef x * Ψ x j : ℝ) : ℂ)) volume ∧
          IntegrableOn
            (fun x : Coord => w x i * ((coef x * qPeriodize p.c (fun y => Ψ y j) x.1 x.2 : ℝ) : ℂ))
            (Icc a b ×ˢ B0579.cell p.c) volume ∧
          ∫ x : Coord, w x i * ((coef x * Ψ x j : ℝ) : ℂ) =
            ∫ p_x in Icc a b ×ˢ B0579.cell p.c,
              w p_x i * ((coef p_x * qPeriodize p.c (fun y => Ψ y j) p_x.1 p_x.2 : ℝ) : ℂ) := by
    intro w hw_sm hw_per hw_L2 i j coef hcoef_cont hcoef_per
    let α : Coord → ℝ := fun x => coef x * Ψ x j
    have hα_cont : Continuous α :=
      continuous_mul_cutoff ha hcoef_cont (hΨ.smooth j).smooth.continuous (hΨ_supp j)
    have hα_supp : ∀ x : Coord, (x.1 ∉ Icc a b ∨ R < |x.2.1| ∨ R < |x.2.2|) → α x = 0 := by
      intro x hx; dsimp [α]; rw [hΨ_supp j x hx, mul_zero]
    obtain ⟨hI1, hI2, hEq⟩ :=
      unfold_profile_coord hc0 ha hab hR hw_sm hw_per hw_L2 i hα_cont hα_supp
    have hcongr_prod : ∀ x ∈ Icc a b ×ˢ B0579.cell p.c,
        w x i * (qPeriodize p.c α x.1 x.2 : ℂ) =
          w x i * ((coef x * qPeriodize p.c (fun y => Ψ y j) x.1 x.2 : ℝ) : ℂ) := by
      intro ⟨s, y⟩ ⟨hs, _⟩
      have hs_pos : 0 < s := lt_of_lt_of_le ha hs.1
      rw [qPeriodize_mul_periodic (hcoef_per s hs_pos) y]
    have hI2' : IntegrableOn
        (fun x : Coord => w x i * ((coef x * qPeriodize p.c (fun y => Ψ y j) x.1 x.2 : ℝ) : ℂ))
        (Icc a b ×ˢ B0579.cell p.c) volume :=
      hI2.congr_fun hcongr_prod (measurableSet_Icc.prod (B0579.measurableSet_cell p.c))
    refine ⟨hI1, hI2', ?_⟩
    rw [hEq, ← setIntegral_prod _ hI2]
    exact setIntegral_congr_fun (measurableSet_Icc.prod (B0579.measurableSet_cell p.c)) hcongr_prod
  -- Smoothness and periodicity of the 4 train coefficient families
  have hcv_cont : ∀ k : Fin 2, ContinuousOn (fun x : Coord => p.train.v x.1 x.2 k) (Ioi 0 ×ˢ univ) :=
    fun k => (EuclideanSpace.proj (𝕜 := ℝ) k).continuous.comp_continuousOn
      (p.train.isTrain.smooth_v.continuousOn.mono (prod_mono Ioi_subset_Ici_self Subset.rfl))
  have hcv_per : ∀ (k : Fin 2) (s : ℝ), 0 < s → ∀ y : B0579.Plane,
      p.train.v s (y.1 + p.c, y.2) k = p.train.v s y k :=
    fun k s hs y => (train_v_smper p.train hs k).2 y
  have hcdv_cont : ∀ k i : Fin 2,
      ContinuousOn (fun x : Coord => B0579.pd k (fun y => p.train.v x.1 y i) x.2) (Ioi 0 ×ˢ univ) :=
    fun k i => continuousOn_train_pd_pos p.train k i
  have hcdv_per : ∀ (k i : Fin 2) (s : ℝ), 0 < s → ∀ y : B0579.Plane,
      B0579.pd k (fun w => p.train.v s w i) (y.1 + p.c, y.2) =
        B0579.pd k (fun w => p.train.v s w i) y :=
    fun k i s hs y => ((train_v_smper p.train hs i).pd k).2 y
  -- Apply hunfold_term to all 8 terms (4 for i = 0, 4 for i = 1)
  obtain ⟨hI_1, hIp_1, hE_1⟩ :=
    hunfold_term hzq_sm hzq_per hzq_L2 0 0 (hcv_cont 0) (hcv_per 0)
  obtain ⟨hI_2, hIp_2, hE_2⟩ :=
    hunfold_term hzη_sm hzη_per hzη_L2 0 0 (hcv_cont 1) (hcv_per 1)
  obtain ⟨hI_3, hIp_3, hE_3⟩ :=
    hunfold_term hz_sm hz_per hz_L2 0 0 (hcdv_cont 0 0) (hcdv_per 0 0)
  obtain ⟨hI_4, hIp_4, hE_4⟩ :=
    hunfold_term hz_sm hz_per hz_L2 1 0 (hcdv_cont 1 0) (hcdv_per 1 0)
  obtain ⟨hI_5, hIp_5, hE_5⟩ :=
    hunfold_term hzq_sm hzq_per hzq_L2 1 1 (hcv_cont 0) (hcv_per 0)
  obtain ⟨hI_6, hIp_6, hE_6⟩ :=
    hunfold_term hzη_sm hzη_per hzη_L2 1 1 (hcv_cont 1) (hcv_per 1)
  obtain ⟨hI_7, hIp_7, hE_7⟩ :=
    hunfold_term hz_sm hz_per hz_L2 0 1 (hcdv_cont 0 1) (hcdv_per 0 1)
  obtain ⟨hI_8, hIp_8, hE_8⟩ :=
    hunfold_term hz_sm hz_per hz_L2 1 1 (hcdv_cont 1 1) (hcdv_per 1 1)
  have hcdot_eq : cdot (flatBv p.train z zq zη) Ψ = fun x : Coord =>
      ((zq x 0 * ((p.train.v x.1 x.2 0 * Ψ x 0 : ℝ) : ℂ) +
        zη x 0 * ((p.train.v x.1 x.2 1 * Ψ x 0 : ℝ) : ℂ)) +
       (z x 0 * ((B0579.pd 0 (fun y => p.train.v x.1 y 0) x.2 * Ψ x 0 : ℝ) : ℂ) +
        z x 1 * ((B0579.pd 1 (fun y => p.train.v x.1 y 0) x.2 * Ψ x 0 : ℝ) : ℂ))) +
      ((zq x 1 * ((p.train.v x.1 x.2 0 * Ψ x 1 : ℝ) : ℂ) +
        zη x 1 * ((p.train.v x.1 x.2 1 * Ψ x 1 : ℝ) : ℂ)) +
       (z x 0 * ((B0579.pd 0 (fun y => p.train.v x.1 y 1) x.2 * Ψ x 1 : ℝ) : ℂ) +
        z x 1 * ((B0579.pd 1 (fun y => p.train.v x.1 y 1) x.2 * Ψ x 1 : ℝ) : ℂ))) := by
    funext x
    simp only [cdot, flatBv, Fin.sum_univ_two, PiLp.toLp_apply, B0579.pd, B0579.dir,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    push_cast
    ring
  rw [hcdot_eq]
  have hI_0a := int_add hI_1 hI_2
  have hI_0b := int_add hI_3 hI_4
  have hI_0 := int_add hI_0a hI_0b
  have hI_1a := int_add hI_5 hI_6
  have hI_1b := int_add hI_7 hI_8
  have hI_1tot := int_add hI_1a hI_1b
  have hIp_0a := intOn_add hIp_1 hIp_2
  have hIp_0b := intOn_add hIp_3 hIp_4
  have hIp_0 := intOn_add hIp_0a hIp_0b
  have hIp_1a := intOn_add hIp_5 hIp_6
  have hIp_1b := intOn_add hIp_7 hIp_8
  have hIp_1tot := intOn_add hIp_1a hIp_1b
  have hIp_tot := intOn_add hIp_0 hIp_1tot
  refine ⟨int_add hI_0 hI_1tot, ?_⟩
  rw [integral_add hI_0 hI_1tot, integral_add hI_0a hI_0b,
    integral_add hI_1 hI_2, integral_add hI_3 hI_4,
    integral_add hI_1a hI_1b, integral_add hI_5 hI_6, integral_add hI_7 hI_8,
    hE_1, hE_2, hE_3, hE_4, hE_5, hE_6, hE_7, hE_8,
    ← integral_add hIp_1 hIp_2, ← integral_add hIp_3 hIp_4,
    ← integral_add hIp_0a hIp_0b,
    ← integral_add hIp_5 hIp_6, ← integral_add hIp_7 hIp_8,
    ← integral_add hIp_1a hIp_1b,
    ← integral_add hIp_0 hIp_1tot]
  -- Fixed-slice identity for every s ∈ Icc a b
  refine integrableOn_and_setIntegral_prod_eq measurableSet_Icc hIp_tot fun s hs => ?_
  dsimp only
  have hs_pos : 0 < s := lt_of_lt_of_le ha hs.1
  have hs_Ioc : s ∈ Ioc 0 p.H := ⟨hs_pos, hs.2.trans hbH.le⟩
  let ζ : B0579.Plane → ℝ := φ s
  have hζ : B0579.IsCylTest p.c ζ := isCylTest_qPeriodize hc0 hΦ_test s
  have hqP_Ψ0 : ∀ y : B0579.Plane, qPeriodize p.c (fun w => Ψ w 0) s y = B0579.pd 1 ζ y := by
    intro y
    have heq : (fun w => Ψ w 0) = cpd 2 Φ := funext fun w => (hΨ_Φ w).1
    rw [heq, qPeriodize_cpd2 hc0 hΦ_test s]
  have hqP_Ψ1 : ∀ y : B0579.Plane, qPeriodize p.c (fun w => Ψ w 1) s y = -B0579.pd 0 ζ y := by
    intro y
    have heq : (fun w => Ψ w 1) = fun w => -cpd 1 Φ w := funext fun w => (hΨ_Φ w).2
    rw [heq, qPeriodize_neg, qPeriodize_cpd1 hc0 hΦ_test s]
  simp_rw [hqP_Ψ0, hqP_Ψ1]
  -- Extract slice Biot-Savart, weak derivatives, and Cyl.K a.e. equality
  obtain ⟨hbs, hweak, hK_ae⟩ := hz_slice s hs_Ioc
  have hz0_mem : MemLp (fun y => z (s, y) 0) 2 (volume.restrict (B0579.cell p.c)) := hbs.1 0
  have hz1_mem : MemLp (fun y => z (s, y) 1) 2 (volume.restrict (B0579.cell p.c)) := hbs.1 1
  have hv0_sm : SmPer p.c (fun y => p.train.v s y 0) := train_v_smper p.train hs_pos 0
  have hv1_sm : SmPer p.c (fun y => p.train.v s y 1) := train_v_smper p.train hs_pos 1
  have hE_sm : SmPer p.c (B0238.Ec p.train s) := train_Ec_smper p.train hs_pos
  -- Auxiliary cylinder tests at age s
  let χ1 : B0579.Plane → ℝ := fun y => p.train.v s y 0 * B0579.pd 1 ζ y
  let χ2 : B0579.Plane → ℝ := fun y => p.train.v s y 1 * B0579.pd 1 ζ y
  let χ5 : B0579.Plane → ℝ := fun y => -(p.train.v s y 0 * B0579.pd 0 ζ y)
  let χ6 : B0579.Plane → ℝ := fun y => -(p.train.v s y 1 * B0579.pd 0 ζ y)
  let χ3 : B0579.Plane → ℝ := fun y => B0579.pd 0 (fun w => p.train.v s w 0) y * B0579.pd 1 ζ y
  let χ4 : B0579.Plane → ℝ := fun y => B0579.pd 1 (fun w => p.train.v s w 0) y * B0579.pd 1 ζ y
  let χ7 : B0579.Plane → ℝ := fun y => -(B0579.pd 0 (fun w => p.train.v s w 1) y * B0579.pd 0 ζ y)
  let χ8 : B0579.Plane → ℝ := fun y => -(B0579.pd 1 (fun w => p.train.v s w 1) y * B0579.pd 0 ζ y)
  have hχ1 : B0579.IsCylTest p.c χ1 := isCylTest_mul_smper hv0_sm (hζ.pd 1)
  have hχ2 : B0579.IsCylTest p.c χ2 := isCylTest_mul_smper hv1_sm (hζ.pd 1)
  have hχ5 : B0579.IsCylTest p.c χ5 := isCylTest_neg (isCylTest_mul_smper hv0_sm (hζ.pd 0))
  have hχ6 : B0579.IsCylTest p.c χ6 := isCylTest_neg (isCylTest_mul_smper hv1_sm (hζ.pd 0))
  have hχ3 : B0579.IsCylTest p.c χ3 := isCylTest_mul_smper (hv0_sm.pd 0) (hζ.pd 1)
  have hχ4 : B0579.IsCylTest p.c χ4 := isCylTest_mul_smper (hv0_sm.pd 1) (hζ.pd 1)
  have hχ7 : B0579.IsCylTest p.c χ7 := isCylTest_neg (isCylTest_mul_smper (hv1_sm.pd 0) (hζ.pd 0))
  have hχ8 : B0579.IsCylTest p.c χ8 := isCylTest_neg (isCylTest_mul_smper (hv1_sm.pd 1) (hζ.pd 0))
  -- Split the cell integral into the 8 integrable pieces and integrate 1, 2, 5, 6 by parts
  have i1 := ((hweak 0).1.1 χ1 hχ1).2
  have i2 := ((hweak 0).2.1 χ2 hχ2).2
  have i3 := integrableOn_memLp_mul_cylTest hz0_mem hχ3
  have i4 := integrableOn_memLp_mul_cylTest hz1_mem hχ4
  have i5 := ((hweak 1).1.1 χ5 hχ5).2
  have i6 := ((hweak 1).2.1 χ6 hχ6).2
  have i7 := integrableOn_memLp_mul_cylTest hz0_mem hχ7
  have i8 := integrableOn_memLp_mul_cylTest hz1_mem hχ8
  have hcell_split :
      (∫ y in B0579.cell p.c,
        (((zq (s, y) 0 * ((p.train.v s y 0 * B0579.pd 1 ζ y : ℝ) : ℂ) +
           zη (s, y) 0 * ((p.train.v s y 1 * B0579.pd 1 ζ y : ℝ) : ℂ)) +
          (z (s, y) 0 * ((B0579.pd 0 (fun w => p.train.v s w 0) y * B0579.pd 1 ζ y : ℝ) : ℂ) +
           z (s, y) 1 * ((B0579.pd 1 (fun w => p.train.v s w 0) y * B0579.pd 1 ζ y : ℝ) : ℂ))) +
         ((zq (s, y) 1 * ((p.train.v s y 0 * -B0579.pd 0 ζ y : ℝ) : ℂ) +
           zη (s, y) 1 * ((p.train.v s y 1 * -B0579.pd 0 ζ y : ℝ) : ℂ)) +
          (z (s, y) 0 * ((B0579.pd 0 (fun w => p.train.v s w 1) y * -B0579.pd 0 ζ y : ℝ) : ℂ) +
           z (s, y) 1 * ((B0579.pd 1 (fun w => p.train.v s w 1) y * -B0579.pd 0 ζ y : ℝ) : ℂ))))) =
      ((∫ y in B0579.cell p.c, zq (s, y) 0 * (χ1 y : ℂ)) +
       (∫ y in B0579.cell p.c, zη (s, y) 0 * (χ2 y : ℂ)) +
       (∫ y in B0579.cell p.c, z (s, y) 0 * (χ3 y : ℂ)) +
       (∫ y in B0579.cell p.c, z (s, y) 1 * (χ4 y : ℂ))) +
      ((∫ y in B0579.cell p.c, zq (s, y) 1 * (χ5 y : ℂ)) +
       (∫ y in B0579.cell p.c, zη (s, y) 1 * (χ6 y : ℂ)) +
       (∫ y in B0579.cell p.c, z (s, y) 0 * (χ7 y : ℂ)) +
       (∫ y in B0579.cell p.c, z (s, y) 1 * (χ8 y : ℂ))) := by
    have heq : ∀ y : B0579.Plane,
        (((zq (s, y) 0 * ((p.train.v s y 0 * B0579.pd 1 ζ y : ℝ) : ℂ) +
           zη (s, y) 0 * ((p.train.v s y 1 * B0579.pd 1 ζ y : ℝ) : ℂ)) +
          (z (s, y) 0 * ((B0579.pd 0 (fun w => p.train.v s w 0) y * B0579.pd 1 ζ y : ℝ) : ℂ) +
           z (s, y) 1 * ((B0579.pd 1 (fun w => p.train.v s w 0) y * B0579.pd 1 ζ y : ℝ) : ℂ))) +
         ((zq (s, y) 1 * ((p.train.v s y 0 * -B0579.pd 0 ζ y : ℝ) : ℂ) +
           zη (s, y) 1 * ((p.train.v s y 1 * -B0579.pd 0 ζ y : ℝ) : ℂ)) +
          (z (s, y) 0 * ((B0579.pd 0 (fun w => p.train.v s w 1) y * -B0579.pd 0 ζ y : ℝ) : ℂ) +
           z (s, y) 1 * ((B0579.pd 1 (fun w => p.train.v s w 1) y * -B0579.pd 0 ζ y : ℝ) : ℂ)))) =
        (((zq (s, y) 0 * (χ1 y : ℂ) + zη (s, y) 0 * (χ2 y : ℂ)) +
          (z (s, y) 0 * (χ3 y : ℂ) + z (s, y) 1 * (χ4 y : ℂ))) +
         ((zq (s, y) 1 * (χ5 y : ℂ) + zη (s, y) 1 * (χ6 y : ℂ)) +
          (z (s, y) 0 * (χ7 y : ℂ) + z (s, y) 1 * (χ8 y : ℂ)))) := by
      intro y; dsimp [χ1, χ2, χ3, χ4, χ5, χ6, χ7, χ8]; push_cast; ring
    simp_rw [heq]
    rw [integral_add (intOn_add (intOn_add i1 i2) (intOn_add i3 i4))
          (intOn_add (intOn_add i5 i6) (intOn_add i7 i8)),
      integral_add (intOn_add i1 i2) (intOn_add i3 i4), integral_add i1 i2, integral_add i3 i4,
      integral_add (intOn_add i5 i6) (intOn_add i7 i8), integral_add i5 i6, integral_add i7 i8]
    ring
  have hw1 : (∫ y in B0579.cell p.c, zq (s, y) 0 * (χ1 y : ℂ)) =
      -(∫ y in B0579.cell p.c, z (s, y) 0 * (B0579.pd 0 χ1 y : ℂ)) :=
    neg_eq_iff_eq_neg.1 ((hweak 0).1.2 χ1 hχ1).symm
  have hw2 : (∫ y in B0579.cell p.c, zη (s, y) 0 * (χ2 y : ℂ)) =
      -(∫ y in B0579.cell p.c, z (s, y) 0 * (B0579.pd 1 χ2 y : ℂ)) :=
    neg_eq_iff_eq_neg.1 ((hweak 0).2.2 χ2 hχ2).symm
  have hw5 : (∫ y in B0579.cell p.c, zq (s, y) 1 * (χ5 y : ℂ)) =
      -(∫ y in B0579.cell p.c, z (s, y) 1 * (B0579.pd 0 χ5 y : ℂ)) :=
    neg_eq_iff_eq_neg.1 ((hweak 1).1.2 χ5 hχ5).symm
  have hw6 : (∫ y in B0579.cell p.c, zη (s, y) 1 * (χ6 y : ℂ)) =
      -(∫ y in B0579.cell p.c, z (s, y) 1 * (B0579.pd 1 χ6 y : ℂ)) :=
    neg_eq_iff_eq_neg.1 ((hweak 1).2.2 χ6 hχ6).symm
  rw [hcell_split, hw1, hw2, hw5, hw6]
  -- Recombine all 8 z-terms into one cell integral and use pointwise curl/product-rule identity
  have id1 := integrableOn_memLp_mul_cylTest hz0_mem (hχ1.pd 0)
  have id2 := integrableOn_memLp_mul_cylTest hz0_mem (hχ2.pd 1)
  have id5 := integrableOn_memLp_mul_cylTest hz1_mem (hχ5.pd 0)
  have id6 := integrableOn_memLp_mul_cylTest hz1_mem (hχ6.pd 1)
  let wF : B0579.Plane → ℝ := fun y =>
    p.train.v s y 0 * B0579.pd 0 ζ y + p.train.v s y 1 * B0579.pd 1 ζ y
  let Eζ : B0579.Plane → ℝ := fun y => B0238.Ec p.train s y * ζ y
  let ψE0 : B0579.Plane → ℝ := fun y => ζ y * B0579.pd 0 (B0238.Ec p.train s) y
  let ψE1 : B0579.Plane → ℝ := fun y => ζ y * B0579.pd 1 (B0238.Ec p.train s) y
  have hwF_cyl : B0579.IsCylTest p.c wF :=
    isCylTest_add (isCylTest_mul_smper hv0_sm (hζ.pd 0)) (isCylTest_mul_smper hv1_sm (hζ.pd 1))
  have hEζ_cyl : B0579.IsCylTest p.c Eζ := isCylTest_mul_smper hE_sm hζ
  have hψE0_cyl : B0579.IsCylTest p.c ψE0 := by
    have heq : ψE0 = fun y => B0579.pd 0 (B0238.Ec p.train s) y * ζ y :=
      funext fun y => mul_comm _ _
    rw [heq]; exact isCylTest_mul_smper (hE_sm.pd 0) hζ
  have hψE1_cyl : B0579.IsCylTest p.c ψE1 := by
    have heq : ψE1 = fun y => B0579.pd 1 (B0238.Ec p.train s) y * ζ y :=
      funext fun y => mul_comm _ _
    rw [heq]; exact isCylTest_mul_smper (hE_sm.pd 1) hζ
  have iwF0 := integrableOn_memLp_mul_cylTest hz0_mem (hwF_cyl.pd 1)
  have iwF1 := integrableOn_memLp_mul_cylTest hz1_mem (hwF_cyl.pd 0)
  have iE0 := integrableOn_memLp_mul_cylTest hz0_mem hψE0_cyl
  have iE1 := integrableOn_memLp_mul_cylTest hz1_mem hψE1_cyl
  have iEζ0 := integrableOn_memLp_mul_cylTest hz0_mem (hEζ_cyl.pd 0)
  have iEζ1 := integrableOn_memLp_mul_cylTest hz1_mem (hEζ_cyl.pd 1)
  have hcomb_lhs :
      (-(∫ y in B0579.cell p.c, z (s, y) 0 * (B0579.pd 0 χ1 y : ℂ)) +
       -(∫ y in B0579.cell p.c, z (s, y) 0 * (B0579.pd 1 χ2 y : ℂ)) +
       (∫ y in B0579.cell p.c, z (s, y) 0 * (χ3 y : ℂ)) +
       (∫ y in B0579.cell p.c, z (s, y) 1 * (χ4 y : ℂ))) +
      (-(∫ y in B0579.cell p.c, z (s, y) 1 * (B0579.pd 0 χ5 y : ℂ)) +
       -(∫ y in B0579.cell p.c, z (s, y) 1 * (B0579.pd 1 χ6 y : ℂ)) +
       (∫ y in B0579.cell p.c, z (s, y) 0 * (χ7 y : ℂ)) +
       (∫ y in B0579.cell p.c, z (s, y) 1 * (χ8 y : ℂ))) =
      ∫ y in B0579.cell p.c,
        (((-(z (s, y) 0 * (B0579.pd 0 χ1 y : ℂ)) + -(z (s, y) 0 * (B0579.pd 1 χ2 y : ℂ))) +
          (z (s, y) 0 * (χ3 y : ℂ) + z (s, y) 1 * (χ4 y : ℂ))) +
         ((-(z (s, y) 1 * (B0579.pd 0 χ5 y : ℂ)) + -(z (s, y) 1 * (B0579.pd 1 χ6 y : ℂ))) +
          (z (s, y) 0 * (χ7 y : ℂ) + z (s, y) 1 * (χ8 y : ℂ)))) := by
    rw [← integral_neg, ← integral_neg, ← integral_neg, ← integral_neg,
      ← integral_add (intOn_neg id1) (intOn_neg id2),
      ← integral_add (intOn_add (intOn_neg id1) (intOn_neg id2)) i3,
      ← integral_add (intOn_add (intOn_add (intOn_neg id1) (intOn_neg id2)) i3) i4,
      ← integral_add (intOn_neg id5) (intOn_neg id6),
      ← integral_add (intOn_add (intOn_neg id5) (intOn_neg id6)) i7,
      ← integral_add (intOn_add (intOn_add (intOn_neg id5) (intOn_neg id6)) i7) i8,
      ← integral_add
        (intOn_add (intOn_add (intOn_add (intOn_neg id1) (intOn_neg id2)) i3) i4)
        (intOn_add (intOn_add (intOn_add (intOn_neg id5) (intOn_neg id6)) i7) i8)]
    refine setIntegral_congr_fun (B0579.measurableSet_cell p.c) fun y _ => ?_
    ring
  have hpt_slice : ∀ y : B0579.Plane,
      (((-(z (s, y) 0 * (B0579.pd 0 χ1 y : ℂ)) + -(z (s, y) 0 * (B0579.pd 1 χ2 y : ℂ))) +
        (z (s, y) 0 * (χ3 y : ℂ) + z (s, y) 1 * (χ4 y : ℂ))) +
       ((-(z (s, y) 1 * (B0579.pd 0 χ5 y : ℂ)) + -(z (s, y) 1 * (B0579.pd 1 χ6 y : ℂ))) +
        (z (s, y) 0 * (χ7 y : ℂ) + z (s, y) 1 * (χ8 y : ℂ)))) =
      -(z (s, y) 0 * (B0579.pd 1 wF y : ℂ) - z (s, y) 1 * (B0579.pd 0 wF y : ℂ)) +
        (z (s, y) 0 * (ψE0 y : ℂ) + z (s, y) 1 * (ψE1 y : ℂ)) -
        (z (s, y) 0 * (B0579.pd 0 Eζ y : ℂ) + z (s, y) 1 * (B0579.pd 1 Eζ y : ℂ)) := by
    intro y
    have dv0 : Differentiable ℝ (fun w => p.train.v s w 0) := hv0_sm.1.differentiable (by simp)
    have dv1 : Differentiable ℝ (fun w => p.train.v s w 1) := hv1_sm.1.differentiable (by simp)
    have dE : Differentiable ℝ (B0238.Ec p.train s) := hE_sm.1.differentiable (by simp)
    have dζ := hζ.differentiable
    have dζ0 := (hζ.pd 0).differentiable
    have dζ1 := (hζ.pd 1).differentiable
    have p_χ1 : B0579.pd 0 χ1 y =
        B0579.pd 0 (fun w => p.train.v s w 0) y * B0579.pd 1 ζ y +
          p.train.v s y 0 * B0579.pd 0 (B0579.pd 1 ζ) y := pd_mul_at dv0 dζ1 0 y
    have p_χ2 : B0579.pd 1 χ2 y =
        B0579.pd 1 (fun w => p.train.v s w 1) y * B0579.pd 1 ζ y +
          p.train.v s y 1 * B0579.pd 1 (B0579.pd 1 ζ) y := pd_mul_at dv1 dζ1 1 y
    have p_χ5 : B0579.pd 0 χ5 y =
        -(B0579.pd 0 (fun w => p.train.v s w 0) y * B0579.pd 0 ζ y +
          p.train.v s y 0 * B0579.pd 0 (B0579.pd 0 ζ) y) := by
      have h := congr_fun (pd_neg_fun (fun w => p.train.v s w 0 * B0579.pd 0 ζ w) 0) y
      dsimp [χ5]
      rw [h, pd_mul_at dv0 dζ0 0 y]
    have p_χ6 : B0579.pd 1 χ6 y =
        -(B0579.pd 1 (fun w => p.train.v s w 1) y * B0579.pd 0 ζ y +
          p.train.v s y 1 * B0579.pd 1 (B0579.pd 0 ζ) y) := by
      have h := congr_fun (pd_neg_fun (fun w => p.train.v s w 1 * B0579.pd 0 ζ w) 1) y
      dsimp [χ6]
      rw [h, pd_mul_at dv1 dζ0 1 y]
    have dv0ζ0 : Differentiable ℝ (fun w => p.train.v s w 0 * B0579.pd 0 ζ w) := dv0.mul dζ0
    have dv1ζ1 : Differentiable ℝ (fun w => p.train.v s w 1 * B0579.pd 1 ζ w) := dv1.mul dζ1
    have p_wF0 : B0579.pd 0 wF y =
        (B0579.pd 0 (fun w => p.train.v s w 0) y * B0579.pd 0 ζ y +
          p.train.v s y 0 * B0579.pd 0 (B0579.pd 0 ζ) y) +
        (B0579.pd 0 (fun w => p.train.v s w 1) y * B0579.pd 1 ζ y +
          p.train.v s y 1 * B0579.pd 0 (B0579.pd 1 ζ) y) := by
      have h := congr_fun (pd_add_fun dv0ζ0 dv1ζ1 0) y
      dsimp [wF]
      rw [h, pd_mul_at dv0 dζ0 0 y, pd_mul_at dv1 dζ1 0 y]
    have p_wF1 : B0579.pd 1 wF y =
        (B0579.pd 1 (fun w => p.train.v s w 0) y * B0579.pd 0 ζ y +
          p.train.v s y 0 * B0579.pd 1 (B0579.pd 0 ζ) y) +
        (B0579.pd 1 (fun w => p.train.v s w 1) y * B0579.pd 1 ζ y +
          p.train.v s y 1 * B0579.pd 1 (B0579.pd 1 ζ) y) := by
      have h := congr_fun (pd_add_fun dv0ζ0 dv1ζ1 1) y
      dsimp [wF]
      rw [h, pd_mul_at dv0 dζ0 1 y, pd_mul_at dv1 dζ1 1 y]
    have p_Eζ0 : B0579.pd 0 Eζ y =
        B0579.pd 0 (B0238.Ec p.train s) y * ζ y + B0238.Ec p.train s y * B0579.pd 0 ζ y :=
      pd_mul_at dE dζ 0 y
    have p_Eζ1 : B0579.pd 1 Eζ y =
        B0579.pd 1 (B0238.Ec p.train s) y * ζ y + B0238.Ec p.train s y * B0579.pd 1 ζ y :=
      pd_mul_at dE dζ 1 y
    have hcomm : B0579.pd 1 (B0579.pd 0 ζ) y = B0579.pd 0 (B0579.pd 1 ζ) y :=
      congr_fun (pd_comm_plane hζ.smooth 1 0) y
    have hE_val : B0238.Ec p.train s y =
        B0579.pd 0 (fun w => p.train.v s w 1) y - B0579.pd 1 (fun w => p.train.v s w 0) y :=
      congr_fun (train_Ec_eq p.train hs_pos) y
    rw [p_χ1, p_χ2, p_χ5, p_χ6, p_wF0, p_wF1, p_Eζ0, p_Eζ1, hcomm, hE_val]
    dsimp [χ3, χ4, χ7, χ8, ψE0, ψE1]
    push_cast
    ring
  rw [hcomb_lhs]
  simp_rw [hpt_slice]
  rw [integral_sub
        (intOn_add (intOn_neg (intOn_sub iwF0 iwF1)) (intOn_add iE0 iE1))
        (intOn_add iEζ0 iEζ1),
    integral_add (intOn_neg (intOn_sub iwF0 iwF1)) (intOn_add iE0 iE1),
    integral_neg, ← hbs.2.2 wF hwF_cyl, hbs.2.1 Eζ hEζ_cyl, sub_zero]
  congr 1
  -- Identify z(s, y) with Cyl.K p.c (om s) y a.e. on B0579.cell p.c
  have hK_congr : (fun y => z (s, y) 0 * (ψE0 y : ℂ) + z (s, y) 1 * (ψE1 y : ℂ)) =ᵐ[
      volume.restrict (B0579.cell p.c)]
      fun y => (((Cyl.K p.c (om s) y 0 * ψE0 y + Cyl.K p.c (om s) y 1 * ψE1 y : ℝ) : ℂ)) := by
    filter_upwards [hK_ae] with y hy
    have hy0 : (((Cyl.K p.c (om s) y 0 : ℝ) : ℂ)) = z (s, y) 0 := congr_fun hy 0
    have hy1 : (((Cyl.K p.c (om s) y 1 : ℝ) : ℂ)) = z (s, y) 1 := congr_fun hy 1
    rw [← hy0, ← hy1]
    push_cast
    ring
  rw [integral_congr_ae hK_congr]
  exact integral_ofReal

/-! ## 5. Body-source curl pairing and main assembly of `greenVorticityToVelocityEq_proof` -/

private theorem hasWeakFO_qShift {c : ℝ} (w : Fin 3 → ℝ) {u g : Coord → ℂ}
    (h : HasWeakFO (fun _ => w) dZero u g) :
    HasWeakFO (fun _ => w) dZero (fun x => u (qShift c x)) (fun x => g (qShift c x)) := by
  let e : Coord := (0, (c, 0))
  have hqe : qShift c = fun x => x + e := by
    funext x; ext <;> simp [qShift, e]
  have hS : ∀ x : Coord, qShift c x + -e = x := by
    intro x; rw [hqe]; simp
  have hmp : MeasurePreserving (qShift c) (volume : Measure Coord) volume := by
    rw [hqe]; exact measurePreserving_add_right volume e
  have hem : MeasurableEmbedding (qShift c) := by
    rw [hqe]; exact (Homeomorph.addRight e).measurableEmbedding
  have htest : ∀ φ, IsCoordTest φ → IsCoordTest (fun y => φ (y + -e)) := by
    intro φ hφ
    refine ⟨hφ.smooth.comp (contDiff_id.add contDiff_const),
      hφ.compact.comp_homeomorph (Homeomorph.addRight (-e)), ?_⟩
    have hc : IsClosed ((fun y : Coord => y + -e) ⁻¹' tsupport φ) :=
      (isClosed_tsupport φ).preimage (continuous_id.add continuous_const)
    have hsub : tsupport (fun y => φ (y + -e)) ⊆ (fun y : Coord => y + -e) ⁻¹' tsupport φ :=
      closure_minimal (fun y hy => subset_tsupport φ (by simpa [Function.mem_support] using hy)) hc
    intro y hy
    simpa [e] using hφ.supp (hsub hy)
  have hTr_const : ∀ (ψ : Coord → ℝ), Differentiable ℝ ψ → ∀ y : Coord,
      coordTranspose (fun _ => w) dZero ψ y = -(∑ j : Fin 3, w j * cpd j ψ y) := by
    intro ψ hψ y
    simp only [coordTranspose, dZero, zero_mul, add_zero]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [cpd]
    rw [fderiv_const_mul (hψ y)]
    simp
  have hTr : ∀ φ, IsCoordTest φ → ∀ y : Coord,
      coordTranspose (fun _ => w) dZero (fun z => φ (z + -e)) y =
        coordTranspose (fun _ => w) dZero φ (y + -e) := by
    intro φ hφ y
    have hd : Differentiable ℝ φ := hφ.smooth.differentiable (by simp)
    have hd' : Differentiable ℝ (fun z => φ (z + -e)) := hd.comp (differentiable_id.add_const _)
    rw [hTr_const _ hd', hTr_const _ hd]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [cpd]
    rw [fderiv_comp_add_right]
  refine ⟨fun φ hφ => ⟨?_, ?_⟩, fun φ hφ => ?_⟩
  · have hI : Integrable (fun y => u y * ((coordTranspose (fun _ => w) dZero φ (y + -e) : ℝ) : ℂ)) :=
      (h.1 _ (htest φ hφ)).1.congr (Eventually.of_forall fun y => by simp [hTr φ hφ y])
    exact ((hmp.integrable_comp_emb hem).2 hI).congr
      (Eventually.of_forall fun x => by simp [Function.comp, hS])
  · have hI := (h.1 _ (htest φ hφ)).2
    exact ((hmp.integrable_comp_emb hem).2 hI).congr
      (Eventually.of_forall fun x => by simp [Function.comp, hS])
  · have e1 : ∫ x, g (qShift c x) * (φ x : ℂ) = ∫ y, g y * (φ (y + -e) : ℂ) := by
      simpa [hS] using hmp.integral_comp hem (fun y => g y * (φ (y + -e) : ℂ))
    have e2 : ∫ x, u (qShift c x) * (coordTranspose (fun _ => w) dZero φ x : ℂ) =
        ∫ y, u y * ((coordTranspose (fun _ => w) dZero φ (y + -e) : ℝ) : ℂ) := by
      simpa [hS] using hmp.integral_comp hem
        (fun y => u y * ((coordTranspose (fun _ => w) dZero φ (y + -e) : ℝ) : ℂ))
    rw [e1, e2, h.2 _ (htest φ hφ)]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp [hTr φ hφ y]

private theorem qPeriodic_of_hasWeakVec_const {c : ℝ} (w : Fin 3 → ℝ) {u g : CProf}
    (hu : QPeriodic c u) (hw : HasWeakVec (fun _ => w) dZero u g) :
    QPeriodic c g := by
  have hshift : HasWeakVec (fun _ => w) dZero (fun x => u (qShift c x))
      (fun x => g (qShift c x)) := fun i => hasWeakFO_qShift w (hw i)
  have hu_ae : ∀ᵐ x : Coord, 0 < x.1 → u (qShift c x) = u x := QPerHalf.ae_imp hu
  have hw' : HasWeakVec (fun _ => w) dZero (fun x => u (qShift c x)) g :=
    hasWeakVec_congr hu_ae (Eventually.of_forall fun _ _ => rfl) hw
  exact QPerHalf.of_ae_imp (GradBoundHelp.hasWeakVec_unique hshift hw')

private theorem coord_bodySource_eq {m : ℝ} (hm0 : 0 ≤ m) {p : Params} (hc0 : 0 < p.c)
    {f : ℝ → Xmc p.c m} (hf_int : IntegrableOn f (Ioc 0 p.H) volume)
    {b0 b0q b0η g gq gη : CProf}
    (hg_per : QPeriodic p.c g)
    (hg_wq : HasWeakVec vQ0 dZero g gq)
    (hg_wη : HasWeakVec vEta dZero g gη)
    (hg_body : IsBodySource p.train b0 b0q b0η g)
    (hf_curl : ∀ᵐ s ∂volume, s ∈ Ioc 0 p.H →
      ∀ᵐ x ∂volume, x ∈ B0579.cell p.c →
        ((f s x : ℝ) : ℂ) = profCurl gq gη (s, x))
    {Ψ : Coord → Fin 2 → ℝ} (hΨ : IsPlanarSolTest Ψ)
    {Φ : Coord → ℝ} {a b R : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbH : b < p.H) (hR : 0 < R)
    (hΦ_test : IsCoordTest Φ)
    (hΦ_box : tsupport Φ ⊆ Icc a b ×ˢ (Icc (-R) R ×ˢ Icc (-R) R))
    (hΨ_Φ : ∀ x : Coord, Ψ x 0 = cpd 2 Φ x ∧ Ψ x 1 = -cpd 1 Φ x) :
    Integrable (cdot g Ψ) volume ∧
      ∫ x, cdot g Ψ x =
        ∫ s in Icc a b, ((∫ y in B0579.cell p.c, f s y * qPeriodize p.c Φ s y : ℝ) : ℂ) := by
  have hInt_g : Integrable (cdot g Ψ) volume := (hg_body.equation Ψ hΨ).1
  refine ⟨hInt_g, ?_⟩
  -- Step 1: Integrate by parts against Φ via HasWeakVec
  have hctQ : ∀ x : Coord, coordTranspose vQ0 dZero Φ x = -cpd 1 Φ x :=
    fun x => coordTranspose_vQ0_vEta 0 Φ x
  have hctE : ∀ x : Coord, coordTranspose vEta dZero Φ x = -cpd 2 Φ x :=
    fun x => coordTranspose_vQ0_vEta 1 Φ x
  have hIq1 := ((hg_wq 1).1 Φ hΦ_test).2
  have hIη0 := ((hg_wη 0).1 Φ hΦ_test).2
  have hIg_q : Integrable (fun x => g x 1 * (cpd 1 Φ x : ℂ)) volume := by
    have h1 := ((hg_wq 1).1 Φ hΦ_test).1
    have heq : (fun x => g x 1 * (coordTranspose vQ0 dZero Φ x : ℂ)) =
        fun x => -(g x 1 * (cpd 1 Φ x : ℂ)) := by
      funext x; rw [hctQ x]; push_cast; ring
    rw [heq] at h1
    exact h1.neg.congr (Eventually.of_forall fun x => neg_neg _)
  have hIg_η : Integrable (fun x => g x 0 * (cpd 2 Φ x : ℂ)) volume := by
    have h1 := ((hg_wη 0).1 Φ hΦ_test).1
    have heq : (fun x => g x 0 * (coordTranspose vEta dZero Φ x : ℂ)) =
        fun x => -(g x 0 * (cpd 2 Φ x : ℂ)) := by
      funext x; rw [hctE x]; push_cast; ring
    rw [heq] at h1
    exact h1.neg.congr (Eventually.of_forall fun x => neg_neg _)
  have hibp : ∫ x, cdot g Ψ x = ∫ x, profCurl gq gη x * (Φ x : ℂ) := by
    have hcdot : cdot g Ψ = fun x => g x 0 * (cpd 2 Φ x : ℂ) - g x 1 * (cpd 1 Φ x : ℂ) := by
      funext x
      rw [cdot, Fin.sum_univ_two, (hΨ_Φ x).1, (hΨ_Φ x).2]
      push_cast; ring
    have eq_q := (hg_wq 1).2 Φ hΦ_test
    have eq_η := (hg_wη 0).2 Φ hΦ_test
    have heq_q' : (fun x => g x 1 * (coordTranspose vQ0 dZero Φ x : ℂ)) =
        fun x => -(g x 1 * (cpd 1 Φ x : ℂ)) := by
      funext x; rw [hctQ x]; push_cast; ring
    have heq_η' : (fun x => g x 0 * (coordTranspose vEta dZero Φ x : ℂ)) =
        fun x => -(g x 0 * (cpd 2 Φ x : ℂ)) := by
      funext x; rw [hctE x]; push_cast; ring
    rw [heq_q', integral_neg] at eq_q
    rw [heq_η', integral_neg] at eq_η
    rw [hcdot, integral_sub hIg_η hIg_q]
    have hcurl_sub : ∫ x, profCurl gq gη x * (Φ x : ℂ) =
        (∫ x, gq x 1 * (Φ x : ℂ)) - (∫ x, gη x 0 * (Φ x : ℂ)) := by
      unfold profCurl
      rw [← integral_sub hIq1 hIη0]
      congr 1; funext x; ring
    rw [hcurl_sub, eq_q, eq_η]
    ring
  -- Step 2: Cut off profCurl gq gη to Upos = Ioi 0 ×ˢ univ and unfold via qPeriodize
  let u₀ : Coord → ℂ := DriftWeakSHelp.Upos.indicator (profCurl gq gη)
  have hUpos_meas : MeasurableSet DriftWeakSHelp.Upos :=
    measurableSet_Ioi.prod MeasurableSet.univ
  have hloc_curl : LocallyIntegrableOn (profCurl gq gη) DriftWeakSHelp.Upos volume :=
    (DriftWeakSHelp.locInt_of_tests _ (fun φ hφ => ((hg_wq 1).1 φ hφ).2)).sub
      (DriftWeakSHelp.locInt_of_tests _ (fun φ hφ => ((hg_wη 0).1 φ hφ).2))
  have hu₀_meas : AEStronglyMeasurable u₀ volume :=
    (aestronglyMeasurable_indicator_iff hUpos_meas).2 hloc_curl.aestronglyMeasurable
  have hgq_per : QPeriodic p.c gq := qPeriodic_of_hasWeakVec_const ![0, 1, 0] hg_per hg_wq
  have hgη_per : QPeriodic p.c gη := qPeriodic_of_hasWeakVec_const ![0, 0, 1] hg_per hg_wη
  have hu₀_per : ∀ᵐ x ∂(volume.restrict {x : Coord | 0 < x.1}), u₀ (qShift p.c x) = u₀ x := by
    rw [ae_restrict_iff' QPerHalf.measurableSet_pos]
    filter_upwards [QPerHalf.ae_imp hgq_per, QPerHalf.ae_imp hgη_per] with x hxq hxη hpos
    have hxU : x ∈ DriftWeakSHelp.Upos := ⟨hpos, trivial⟩
    have hxsU : qShift p.c x ∈ DriftWeakSHelp.Upos := ⟨hpos, trivial⟩
    dsimp [u₀]
    rw [Set.indicator_of_mem hxsU, Set.indicator_of_mem hxU]
    unfold profCurl
    rw [hxq hpos, hxη hpos]
  have hsub_ab : Icc a b ⊆ Ioc 0 p.H :=
    fun s hs => ⟨lt_of_lt_of_le ha hs.1, hs.2.trans hbH.le⟩
  have hu₀_slice_ae : ∀ᵐ s ∂(volume.restrict (Icc a b)),
      (fun y => u₀ (s, y)) =ᵐ[volume.restrict (B0579.cell p.c)] fun y => ((f s y : ℝ) : ℂ) := by
    rw [ae_restrict_iff' measurableSet_Icc]
    filter_upwards [hf_curl] with s hs hs_ab
    have hs_pos : 0 < s := lt_of_lt_of_le ha hs_ab.1
    rw [EventuallyEq, ae_restrict_iff' (B0579.measurableSet_cell p.c)]
    filter_upwards [hs (hsub_ab hs_ab)] with y hy hy_cell
    have hU : ((s, y) : Coord) ∈ DriftWeakSHelp.Upos := ⟨hs_pos, trivial⟩
    dsimp [u₀]
    rw [Set.indicator_of_mem hU, ← hy hy_cell]
  have hu₀_loc : (∫⁻ s in Icc a b,
      eLpNorm (fun y => u₀ (s, y)) 2 (volume.restrict (B0579.cell p.c))) < ⊤ := by
    have hae_le : ∀ᵐ s ∂(volume.restrict (Icc a b)),
        eLpNorm (fun y => u₀ (s, y)) 2 (volume.restrict (B0579.cell p.c)) ≤ ‖f s‖ₑ := by
      filter_upwards [hu₀_slice_ae] with s hs_eq
      rw [eLpNorm_congr_ae hs_eq]
      have hreal : eLpNorm (fun y => ((f s y : ℝ) : ℂ)) 2 (volume.restrict (B0579.cell p.c)) =
          eLpNorm (⇑(f s)) 2 (volume.restrict (B0579.cell p.c)) :=
        eLpNorm_congr_norm_ae (Eventually.of_forall fun y => Complex.norm_real (f s y))
      rw [hreal]
      exact CCP.eLpNorm_two_le_Xmc hm0 (f s)
    calc ∫⁻ s in Icc a b, eLpNorm (fun y => u₀ (s, y)) 2 (volume.restrict (B0579.cell p.c))
        ≤ ∫⁻ s in Icc a b, ‖f s‖ₑ := lintegral_mono_ae hae_le
      _ ≤ ∫⁻ s in Ioc 0 p.H, ‖f s‖ₑ := lintegral_mono_set hsub_ab
      _ < ⊤ := hf_int.2
  have hΦ_supp : ∀ x : Coord, (x.1 ∉ Icc a b ∨ R < |x.2.1| ∨ R < |x.2.2|) → Φ x = 0 :=
    fun x hx => notMem_box_vanish hΦ_box x hx
  obtain ⟨_, _, hunf⟩ := integrable_and_integral_coord_eq_cell_qPeriodize hc0 ha hab hR
    hu₀_meas hu₀_per hu₀_loc hΦ_test.smooth.continuous hΦ_supp
  have hu₀_eq_curl : (fun x : Coord => profCurl gq gη x * (Φ x : ℂ)) =
      fun x : Coord => u₀ x * (Φ x : ℂ) := by
    funext x
    by_cases hpos : 0 < x.1
    · have hxU : x ∈ DriftWeakSHelp.Upos := ⟨hpos, trivial⟩
      dsimp [u₀]; rw [Set.indicator_of_mem hxU]
    · have h0 : Φ x = 0 :=
        hΦ_supp x (Or.inl fun h => absurd (lt_of_lt_of_le ha h.1) hpos)
      simp [h0]
  rw [hibp, hu₀_eq_curl, hunf]
  refine integral_congr_ae ?_
  filter_upwards [hu₀_slice_ae] with s hs_eq
  have hmul_eq : (fun y => u₀ (s, y) * (qPeriodize p.c Φ s y : ℂ)) =ᵐ[
      volume.restrict (B0579.cell p.c)]
      fun y => (((f s y * qPeriodize p.c Φ s y : ℝ) : ℂ)) := by
    filter_upwards [hs_eq] with y hy
    rw [hy]
    push_cast; rfl
  rw [integral_congr_ae hmul_eq]
  exact integral_ofReal

end VelocityEqAux

/-- **Proof of `GreenVorticityToVelocityEq` (`PartII-b:F6/2/3`, SP 2216–2222, 2258–2268)**:
unconditionally converts the forced coupled cylinder vorticity weak equation for `om` and
`IsBodySource` for `g` (with `f = curl g`) into the planar-solenoidal velocity equation
`IsMeridionalCorrectionOn.equation` on `(0, p.H) × ℝ²`. -/
theorem greenVorticityToVelocityEq_proof :
    UnforcedLeray.Short.IIb.GreenVorticityUncurlNeeded.GreenVorticityToVelocityEq := by
  open VelocityEqAux TailPeriodizeAux in
  intro m hm p d dm dp _hbg hc1 hH om f hom_cont hf_int _hom_circ hom_weak
    z zq zη hz_sm hzq_sm hzη_sm hz_per hzq_per hzη_per _hz_wq _hz_wη _hz_sol hz_H1 hz_slice
    b0 b0q b0η g gq gη _hb0 hg_per hg_wq hg_wη hg_body _hg_meas _hg_lp hf_curl
    Ψ hΨ hΨ_supp
  have hm_half : 1 / 2 < m := by linarith
  have hm0 : 0 ≤ m := by linarith
  have hc0 : 0 < p.c := by linarith
  obtain ⟨Φ, a, b, R, ha, hab, hbH, hR, hΦ_test, hΦ_box, hΨ_Φ⟩ :=
    exists_streamPot hH hΨ hΨ_supp
  obtain ⟨hL1_int, hL2_int, hL3_int, htime_eq⟩ :=
    time_step_identity hm_half hc1 hH hom_cont hf_int hom_weak ha hab hbH hR hΦ_test hΦ_box
  obtain ⟨hInt_mt, hAmt_int, heq_mt⟩ :=
    coord_meridTranspose_eq hc1 hH hz_sm hz_per hz_H1 hz_slice hΨ ha hab hbH hR hΦ_test hΦ_box hΨ_Φ
  obtain ⟨hInt_bv, hAbv_int, heq_bv⟩ :=
    coord_flatBv_eq hc1 hH hz_sm hzq_sm hzη_sm hz_per hzq_per hzη_per hz_H1 hz_slice
      hΨ ha hab hbH hR hΦ_test hΦ_box hΨ_Φ
  obtain ⟨hInt_g, heq_g⟩ :=
    coord_bodySource_eq hm0 hc0 hf_int hg_per hg_wq hg_wη hg_body hf_curl
      hΨ ha hab hbH hR hΦ_test hΦ_box hΨ_Φ
  refine ⟨hInt_mt, hInt_bv, hInt_g, ?_⟩
  rw [integral_add hInt_mt hInt_bv, heq_mt, heq_bv, heq_g, ← integral_add hAmt_int hAbv_int]
  let φ := qPeriodize p.c Φ
  let φ_s := qPeriodize p.c (cpd 0 Φ)
  -- Combine slice integrals of meridTranspose and flatBv into -L1(s) - L2(s)
  have hslice_comb : ∀ s ∈ Icc a b,
      (-(((∫ y in B0579.cell p.c, om s y * φ_s s y : ℝ) : ℂ)) -
        (((∫ y in B0579.cell p.c, om s y * (p.ν * IIIa.lapP (φ s) y) : ℝ) : ℂ))) +
      ((-∫ y in B0579.cell p.c,
          ((om s y : ℝ) : ℂ) *
            ((p.train.v s y 0 * B0579.pd 0 (φ s) y +
              p.train.v s y 1 * B0579.pd 1 (φ s) y : ℝ) : ℂ)) +
        (((∫ y in B0579.cell p.c,
          (Cyl.K p.c (om s) y 0 * (φ s y * B0579.pd 0 (B0238.Ec p.train s) y) +
            Cyl.K p.c (om s) y 1 * (φ s y * B0579.pd 1 (B0238.Ec p.train s) y)) : ℝ) : ℂ))) =
      -(((∫ y in B0579.cell p.c, om s y * φ_s s y : ℝ) : ℂ)) -
        (((∫ y in B0579.cell p.c, cylCoupledIntegrand p.train (om s) s (φ s) y : ℝ) : ℂ)) := by
    intro s hs
    have hs_pos : 0 < s := lt_of_lt_of_le ha hs.1
    have hs_Icc : s ∈ Icc 0 p.H := ⟨hs_pos.le, hs.2.trans hbH.le⟩
    let ζ : B0579.Plane → ℝ := φ s
    have hζ : B0579.IsCylTest p.c ζ := isCylTest_qPeriodize hc0 hΦ_test s
    have hv0_sm : SmPer p.c (fun y => p.train.v s y 0) := train_v_smper p.train hs_pos 0
    have hv1_sm : SmPer p.c (fun y => p.train.v s y 1) := train_v_smper p.train hs_pos 1
    have hlap_cyl : B0579.IsCylTest p.c (IIIa.lapP ζ) :=
      isCylTest_add ((hζ.pd 0).pd 0) ((hζ.pd 1).pd 1)
    let wF : B0579.Plane → ℝ := fun y =>
      p.train.v s y 0 * B0579.pd 0 ζ y + p.train.v s y 1 * B0579.pd 1 ζ y
    have hwF_cyl : B0579.IsCylTest p.c wF :=
      isCylTest_add (isCylTest_mul_smper hv0_sm (hζ.pd 0)) (isCylTest_mul_smper hv1_sm (hζ.pd 1))
    have hcast_wF : (∫ y in B0579.cell p.c, ((om s y : ℝ) : ℂ) * (wF y : ℂ)) =
        ((∫ y in B0579.cell p.c, om s y * wF y : ℝ) : ℂ) := by
      simp_rw [← Complex.ofReal_mul]; exact integral_ofReal
    rw [show (fun y => ((om s y : ℝ) : ℂ) *
          ((p.train.v s y 0 * B0579.pd 0 (φ s) y +
            p.train.v s y 1 * B0579.pd 1 (φ s) y : ℝ) : ℂ)) =
        fun y => ((om s y : ℝ) : ℂ) * (wF y : ℂ) from rfl, hcast_wF]
    obtain ⟨_, hT_lap⟩ := sourcePairCLM (m := m) hm_half hlap_cyl
    obtain ⟨_, hT_wF⟩ := sourcePairCLM (m := m) hm_half hwF_cyl
    have ilap : IntegrableOn (fun y => om s y * (p.ν * IIIa.lapP ζ y)) (B0579.cell p.c) volume := by
      have h : IntegrableOn (fun y => p.ν * (om s y * IIIa.lapP ζ y)) (B0579.cell p.c) volume :=
        (hT_lap (om s)).1.const_mul p.ν
      exact h.congr_fun (fun y _ => by dsimp; ring) (B0579.measurableSet_cell p.c)
    have iwF : IntegrableOn (fun y => om s y * wF y) (B0579.cell p.c) volume := (hT_wF (om s)).1
    obtain ⟨R_t, B_t, hR_t, hB_t, hRB_t⟩ := CCP.test_bounds hζ
    obtain ⟨Ctr_t, hCtr_t, hCtr_bd⟩ := CCP.train_strip_bounds p.train p.H R_t hH.le
    obtain ⟨_CK_t, _hCK_t, hKb_t⟩ := CCP.K_pair_bound hc1 hm_half R_t (B_t * Ctr_t) hR_t
    have iK_j : ∀ j : Fin 2, IntegrableOn
        (fun y => Cyl.K p.c (om s) y j * (ζ y * B0579.pd j (B0238.Ec p.train s) y))
        (B0579.cell p.c) volume := by
      intro j
      have hmeas : AEStronglyMeasurable
          (fun y => Cyl.K p.c (om s) y j * (ζ y * B0579.pd j (B0238.Ec p.train s) y))
          (volume.restrict (B0579.cell p.c)) :=
        ((CCP.K_comp_aesm hm_half (om s) j).restrict).mul
          (hζ.continuous.measurable.mul (CCP.measurable_pd_Ec p.train s j)).aestronglyMeasurable
      refine ⟨hmeas, ?_⟩
      rw [hasFiniteIntegral_iff_enorm]
      have h1 : ∀ y : B0579.Plane, |y.1| ≤ p.c / 2 →
          |ζ y * B0579.pd j (B0238.Ec p.train s) y| ≤ B_t * Ctr_t := by
        intro y hy1
        by_cases hy2 : |y.2| ≤ R_t
        · rw [abs_mul]
          have b1 := ((hRB_t y).1 hy1).1
          have b2 : |B0579.pd j (B0238.Ec p.train s) y| ≤ Ctr_t := by
            fin_cases j
            · exact (hCtr_bd s hs_Icc y hy1 hy2).2.2.1
            · exact (hCtr_bd s hs_Icc y hy1 hy2).2.2.2
          exact mul_le_mul b1 b2 (abs_nonneg _) (le_trans (abs_nonneg _) b1)
        · rw [((hRB_t y).2 (not_le.1 hy2)).1, zero_mul, abs_zero]
          exact mul_nonneg hB_t hCtr_t
      have h2 : ∀ y : B0579.Plane, R_t < |y.2| →
          ζ y * B0579.pd j (B0238.Ec p.train s) y = 0 := by
        intro y hy2; rw [((hRB_t y).2 hy2).1, zero_mul]
      exact lt_of_le_of_lt (hKb_t _ h1 h2 (om s) j)
        (ENNReal.mul_lt_top ENNReal.ofReal_lt_top enorm_lt_top)
    have iK0 := iK_j 0
    have iK1 := iK_j 1
    have hcell_eq :
        (∫ y in B0579.cell p.c, cylCoupledIntegrand p.train (om s) s ζ y) =
        (∫ y in B0579.cell p.c, om s y * (p.ν * IIIa.lapP ζ y)) +
        (∫ y in B0579.cell p.c, om s y * wF y) -
        (∫ y in B0579.cell p.c,
          (Cyl.K p.c (om s) y 0 * (ζ y * B0579.pd 0 (B0238.Ec p.train s) y) +
            Cyl.K p.c (om s) y 1 * (ζ y * B0579.pd 1 (B0238.Ec p.train s) y))) := by
      have hpt : ∀ y : B0579.Plane,
          cylCoupledIntegrand p.train (om s) s ζ y =
            (om s y * (p.ν * IIIa.lapP ζ y) + om s y * wF y) -
              (Cyl.K p.c (om s) y 0 * (ζ y * B0579.pd 0 (B0238.Ec p.train s) y) +
                Cyl.K p.c (om s) y 1 * (ζ y * B0579.pd 1 (B0238.Ec p.train s) y)) := by
        intro y
        rw [CCP.integrand_eq]
        dsimp [IIIa.lapP, wF]
        ring
      simp_rw [hpt]
      rw [integral_sub (intOn_add ilap iwF) (intOn_add iK0 iK1), integral_add ilap iwF]
    rw [show φ s = ζ from rfl, hcell_eq]
    push_cast
    ring
  rw [setIntegral_congr_fun measurableSet_Icc hslice_comb]
  simp_rw [← Complex.ofReal_neg, ← Complex.ofReal_sub]
  have hcast_lhs :
      (∫ s in Icc a b, (((-∫ y in B0579.cell p.c, om s y * φ_s s y) -
        ∫ y in B0579.cell p.c, cylCoupledIntegrand p.train (om s) s (φ s) y : ℝ) : ℂ)) =
      ((∫ s in Icc a b, ((-∫ y in B0579.cell p.c, om s y * φ_s s y) -
        ∫ y in B0579.cell p.c, cylCoupledIntegrand p.train (om s) s (φ s) y) : ℝ) : ℂ) :=
    integral_ofReal
  have hcast_rhs :
      (∫ s in Icc a b, ((∫ y in B0579.cell p.c, f s y * qPeriodize p.c Φ s y : ℝ) : ℂ)) =
      ((∫ s in Icc a b, ∫ y in B0579.cell p.c, f s y * qPeriodize p.c Φ s y : ℝ) : ℂ) :=
    integral_ofReal
  rw [hcast_lhs, hcast_rhs]
  congr 1
  have hsum0 :
      (∫ s in Icc a b, ∫ y in B0579.cell p.c, om s y * φ_s s y) +
      (∫ s in Icc a b, ∫ y in B0579.cell p.c, cylCoupledIntegrand p.train (om s) s (φ s) y) +
      (∫ s in Icc a b, ∫ y in B0579.cell p.c, f s y * φ s y) = 0 := by
    rw [← integral_add hL1_int hL2_int, ← integral_add (intOn_add hL1_int hL2_int) hL3_int]
    exact htime_eq
  rw [integral_sub (intOn_neg hL1_int) hL2_int, integral_neg]
  change -(∫ s in Icc a b, ∫ y in B0579.cell p.c, om s y * φ_s s y) -
      (∫ s in Icc a b, ∫ y in B0579.cell p.c, cylCoupledIntegrand p.train (om s) s (φ s) y) =
      ∫ s in Icc a b, ∫ y in B0579.cell p.c, f s y * φ s y
  linarith [hsum0]

end UnforcedLeray.Short.IIb.GreenVorticityUncurlNeeded

end
