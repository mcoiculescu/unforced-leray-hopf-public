import UnforcedLeray.Cons.L2.CanonicalBranch.DysonStage
import UnforcedLeray.Lib.EvolutionC.ConstPert
import UnforcedLeray.Lib.BudgetsGronwall.VariationOfConstants

/-!
# Adjoint continuity and boundedness for the canonical first Dyson stage

These are concrete prerequisites for the direct and adjoint strong small-diffusion limit of
Fβ, used in the compact-Duhamel proof of B0112.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped InnerProductSpace ComplexConjugate

namespace UnforcedLeray.Cons.G3b

open UnforcedLeray.B0010 UnforcedLeray.B0012 UnforcedLeray.B0123 UnforcedLeray.Evolution

/-- Every bounded Hermite Yosida truncation of the Gaussian generator is dissipative on the
whole Hilbert space. This is the quadratic-form bridge needed before taking the sharp energy
estimate to the unbounded generator. -/
theorem dyosida_inner_nonpos (N : ℕ) (f : XG) :
    (⟪f, PlanarSpectral.Dyosida N f⟫_ℂ).re ≤ 0 := by
  have hsum := B0094.oscBasis.hasSum_inner_mul_inner f (PlanarSpectral.Dyosida N f)
  have hcoeff : (fun n : ℕ =>
      ⟪f, B0094.oscBasis n⟫_ℂ *
        ⟪B0094.oscBasis n, PlanarSpectral.Dyosida N f⟫_ℂ) =
      fun n : ℕ => -((((n : ℝ) * N / (N + n)) : ℝ) : ℂ) *
        ((‖⟪B0094.oscBasis n, f⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
    funext n
    rw [PlanarSpectral.inner_Dyosida, ← inner_conj_symm f (B0094.oscBasis n)]
    simp only [PlanarSpectral.yosidaMult]
    have hnorm : star ⟪B0094.oscBasis n, f⟫_ℂ * ⟪B0094.oscBasis n, f⟫_ℂ =
        ((‖⟪B0094.oscBasis n, f⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
      calc
        star ⟪B0094.oscBasis n, f⟫_ℂ * ⟪B0094.oscBasis n, f⟫_ℂ =
            ⟪B0094.oscBasis n, f⟫_ℂ * star ⟪B0094.oscBasis n, f⟫_ℂ := by
              rw [mul_comm]
        _ = ((‖⟪B0094.oscBasis n, f⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
          rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    calc
      star ⟪B0094.oscBasis n, f⟫_ℂ *
          (-((((n : ℝ) * N / (N + n)) : ℝ) : ℂ) *
            ⟪B0094.oscBasis n, f⟫_ℂ) =
          -((((n : ℝ) * N / (N + n)) : ℝ) : ℂ) *
            (star ⟪B0094.oscBasis n, f⟫_ℂ * ⟪B0094.oscBasis n, f⟫_ℂ) := by ring
      _ = _ := by rw [hnorm]
  rw [hcoeff] at hsum
  have hre := Complex.hasSum_re hsum
  have hnonpos : ∀ n : ℕ,
      (-((((n : ℝ) * N / (N + n)) : ℝ) : ℂ) *
        ((‖⟪B0094.oscBasis n, f⟫_ℂ‖ ^ 2 : ℝ) : ℂ)).re ≤ 0 := by
    intro n
    simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero]
    have hcoef : 0 ≤ (n : ℝ) * N / (N + n) := by positivity
    have hnorm : 0 ≤ ‖⟪B0094.oscBasis n, f⟫_ℂ‖ ^ 2 := by positivity
    nlinarith
  have hle := hasSum_le hnonpos hre (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℝ)) 0)
  simpa using hle

/-- The actual first Dyson family Fβ has a strongly continuous adjoint on a fixed block. -/
theorem canonicalTransportDysonFamily_adjointContinuous {a b : ℝ} (lam κ : ℂ)
    (β : ℝ → ℝ) (hβi : ∀ s t, IntervalIntegrable β volume s t)
    (hβ0 : ∀ τ, 0 ≤ β τ) (M : ℝ) (hβM : ∀ τ, |β τ| ≤ M)
    (hβsm : AEStronglyMeasurable β (volume.restrict (Set.Icc a b)))
    (hβblock : ∃ B : ℝ, ∀ t ∈ Set.Icc a b, |β t| ≤ B) :
    (canonicalTransportDysonFamily lam κ β hβi hβ0 M hβM hβsm hβblock).AdjointContinuous := by
  change (dyson (freeDiffusionFamily β hβi hβ0 M hβM)
      (transportDysonPert ((-2 * Complex.I) • omegaOp) lam κ β a b hβsm hβblock)).AdjointContinuous
  intro y
  exact Evolution.continuousOn_adjoint_dyson
    (F := freeDiffusionFamily β hβi hβ0 M hβM)
    (A := transportDysonPert ((-2 * Complex.I) • omegaOp) lam κ β a b hβsm hβblock)
    (freeDiffusionFamily_adjointContinuous β hβi hβ0 M hβM)
    (transportDysonPert_adjointMeasurable ((-2 * Complex.I) • omegaOp) lam κ β a b
      hβsm hβblock) y

/-- A block-uniform operator bound for Fβ from the contraction bound on Eβ and the
exponential Dyson estimate. -/
theorem canonicalTransportDysonFamily_norm_le {a b : ℝ}
    (lam κ : ℂ) (β : ℝ → ℝ) (hβi : ∀ s t, IntervalIntegrable β volume s t)
    (hβ0 : ∀ τ, 0 ≤ β τ) (M : ℝ) (hβM : ∀ τ, |β τ| ≤ M)
    (hβsm : AEStronglyMeasurable β (volume.restrict (Set.Icc a b)))
    (hβblock : ∃ B : ℝ, ∀ t ∈ Set.Icc a b, |β t| ≤ B) :
    ∀ s t, a ≤ s → s ≤ t → t ≤ b →
      ‖(canonicalTransportDysonFamily lam κ β hβi hβ0 M hβM hβsm hβblock).U t s‖ ≤
        Real.exp ((‖(-2 * Complex.I) • omegaOp‖ + ‖lam‖ +
          (max (Classical.choose hβblock) 0 * ‖κ‖)) * (t - s)) := by
  intro s t hs hst ht
  let E : EvolutionFamily XG a b := freeDiffusionFamily β hβi hβ0 M hβM
  let A : BoundedPert XG a b :=
    transportDysonPert ((-2 * Complex.I) • omegaOp) lam κ β a b hβsm hβblock
  have hE : ∀ s t, a ≤ s → s ≤ t → t ≤ b →
      ‖E.U t s‖ ≤ 1 * Real.exp (0 * (t - s)) := by
    intro s t hs hst ht
    simpa [E, freeDiffusionFamily, freeDiffusion] using norm_expD_le (∫ r in s..t, β r)
  have hA : ∀ r ∈ Set.Icc a b,
      ‖A.A r‖ ≤ ‖(-2 * Complex.I) • omegaOp‖ + ‖lam‖ +
        (max (Classical.choose hβblock) 0 * ‖κ‖) := by
    intro r hr
    have hb := (Classical.choose_spec hβblock) r hr
    have hcoef : ‖(β r : ℂ)‖ ≤ max (Classical.choose hβblock) 0 := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact hb.trans (le_max_left _ _)
    have hterm : ‖((β r : ℂ) * κ) • (1 : XG →L[ℂ] XG)‖ ≤
        max (Classical.choose hβblock) 0 * ‖κ‖ := by
      rw [norm_smul, norm_mul]
      calc
        ‖(β r : ℂ)‖ * ‖κ‖ * ‖(1 : XG →L[ℂ] XG)‖ ≤
            max (Classical.choose hβblock) 0 * ‖κ‖ * 1 := by
          gcongr
          exact ContinuousLinearMap.norm_id_le
        _ = max (Classical.choose hβblock) 0 * ‖κ‖ := by ring
    have hlam : ‖lam • (1 : XG →L[ℂ] XG)‖ ≤ ‖lam‖ := by
      rw [norm_smul]
      calc
        ‖lam‖ * ‖(1 : XG →L[ℂ] XG)‖ ≤ ‖lam‖ * 1 :=
          mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (norm_nonneg _)
        _ = ‖lam‖ := by ring
    change ‖((-2 * Complex.I) • omegaOp - lam • (1 : XG →L[ℂ] XG)) -
      ((β r : ℂ) * κ) • (1 : XG →L[ℂ] XG)‖ ≤ _
    calc
      _ ≤ ‖(-2 * Complex.I) • omegaOp - lam • (1 : XG →L[ℂ] XG)‖ +
          ‖((β r : ℂ) * κ) • (1 : XG →L[ℂ] XG)‖ := norm_sub_le _ _
      _ ≤ (‖(-2 * Complex.I) • omegaOp‖ + ‖lam • (1 : XG →L[ℂ] XG)‖) +
          max (Classical.choose hβblock) 0 * ‖κ‖ := by
        exact add_le_add (norm_sub_le _ _) hterm
      _ ≤ (‖(-2 * Complex.I) • omegaOp‖ + ‖lam‖) +
          max (Classical.choose hβblock) 0 * ‖κ‖ := by
        linarith [hlam]
      _ = _ := by ring
  have h := Evolution.norm_dyson_le E A hE hA s t hs hst ht
  simpa [canonicalTransportDysonFamily, E, A, Real.exp_zero, one_mul] using h


/-- A finite set of pointwise smallness thresholds has a common positive threshold. -/
private theorem exists_uniform_pos_on_finset {α : Type*} (S : Finset α)
    (P : α → ℝ → Prop)
    (hmono : ∀ x δ δ', δ ≤ δ' → P x δ' → P x δ)
    (hP : ∀ x ∈ S, ∃ δ : ℝ, 0 < δ ∧ P x δ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ S, P x δ := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      exact ⟨1, by norm_num, by simp⟩
  | @insert x S hx ih =>
      have hrest : ∀ y ∈ S, ∃ δ : ℝ, 0 < δ ∧ P y δ := by
        intro y hy
        exact hP y (Finset.mem_insert_of_mem hy)
      obtain ⟨δS, hδS, hPS⟩ := ih hrest
      obtain ⟨δx, hδx, hPx⟩ := hP x (Finset.mem_insert_self x S)
      refine ⟨min δS δx, lt_min hδS hδx, ?_⟩
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hyS
      · exact hmono _ _ _ (min_le_right _ _) hPx
      · exact hmono y _ _ (min_le_left _ _) (hPS y hyS)

/-- Strong small-diffusion convergence is uniform on compact sets of vectors. This finite-net
lemma is the uniformity input for the compact orbit of the bounded limit generator. -/
theorem freeDiffusion_uniform_strong_small_on_compact {B : ℝ} (hB : 0 < B)
    {K : Set XG} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (β : ℝ → ℝ) (s t : ℝ),
      s ≤ t → t - s ≤ B → IntervalIntegrable β volume s t →
      (∀ τ, 0 ≤ β τ) → (∀ τ, β τ ≤ δ) →
      ∀ x ∈ K, ‖freeDiffusion β t s x - x‖ < ε := by
  classical
  by_cases hKn : K.Nonempty
  · obtain ⟨N, hNK, hNfin, hcov⟩ :=
      Metric.finite_approx_of_totallyBounded hK.totallyBounded (ε / 4) (by positivity)
    let Ns : Finset XG := hNfin.toFinset
    have hpoint : ∀ y ∈ Ns, ∃ δ : ℝ, 0 < δ ∧
        ∀ (β : ℝ → ℝ) (s t : ℝ),
          s ≤ t → t - s ≤ B → IntervalIntegrable β volume s t →
          (∀ τ, 0 ≤ β τ) → (∀ τ, β τ ≤ δ) →
          ‖freeDiffusion β t s y - y‖ < ε / 2 := by
      intro y hy
      have hyN' : y ∈ N := (Set.Finite.mem_toFinset hNfin).mp hy
      obtain ⟨δ, hδ, hsmall⟩ := freeDiffusion_uniform_strong_small hB y
        (ε := ε / 2) (by linarith)
      exact ⟨δ, hδ, hsmall⟩
    obtain ⟨δ, hδ, hsmallN⟩ :=
      exists_uniform_pos_on_finset Ns
        (fun y δ => ∀ (β : ℝ → ℝ) (s t : ℝ),
          s ≤ t → t - s ≤ B → IntervalIntegrable β volume s t →
          (∀ τ, 0 ≤ β τ) → (∀ τ, β τ ≤ δ) →
          ‖freeDiffusion β t s y - y‖ < ε / 2) (by
          intro y δ δ' hδδ' hP β s t hst hspan hβi hβ0 hβδ
          exact hP β s t hst hspan hβi hβ0 (fun τ => (hβδ τ).trans hδδ')) hpoint
    refine ⟨δ, hδ, fun β s t hst hspan hβi hβ0 hβδ x hx => ?_⟩
    obtain ⟨y, hyN, hxy⟩ := Set.mem_iUnion₂.mp (hcov hx)
    have hyNs : y ∈ Ns := (Set.Finite.mem_toFinset hNfin).mpr hyN
    have hdist : ‖x - y‖ < ε / 4 := by
      rwa [Metric.mem_ball, dist_eq_norm] at hxy
    have hcenter := hsmallN y hyNs β s t hst hspan hβi hβ0 hβδ
    have hα : 0 ≤ (∫ r in s..t, β r) :=
      intervalIntegral.integral_nonneg hst (fun r _ => hβ0 r)
    have hcontract : ‖freeDiffusion β t s x - freeDiffusion β t s y‖ ≤ ‖x - y‖ := by
      unfold freeDiffusion
      calc
        ‖expD (∫ r in s..t, β r) x - expD (∫ r in s..t, β r) y‖ =
            ‖expD (∫ r in s..t, β r) (x - y)‖ := by rw [map_sub]
        _ ≤ ‖x - y‖ := by
          exact (expD (∫ r in s..t, β r)).le_opNorm (x - y) |>.trans
            (mul_le_of_le_one_left (norm_nonneg _) (norm_expD_le _))
    calc
      ‖freeDiffusion β t s x - x‖ ≤
          ‖freeDiffusion β t s x - freeDiffusion β t s y‖ +
            ‖freeDiffusion β t s y - y‖ + ‖y - x‖ := by
        calc
          _ = ‖(freeDiffusion β t s x - freeDiffusion β t s y) +
                (freeDiffusion β t s y - y) + (y - x)‖ := by
              congr 1
              abel
          _ ≤ ‖freeDiffusion β t s x - freeDiffusion β t s y‖ +
                ‖freeDiffusion β t s y - y‖ + ‖y - x‖ := by
              calc
                _ ≤ ‖(freeDiffusion β t s x - freeDiffusion β t s y) +
                    (freeDiffusion β t s y - y)‖ + ‖y - x‖ := norm_add_le _ _
                _ ≤ (‖freeDiffusion β t s x - freeDiffusion β t s y‖ +
                    ‖freeDiffusion β t s y - y‖) + ‖y - x‖ :=
                    add_le_add (norm_add_le _ _) (le_rfl)
      _ < ε := by
        have hrev : ‖y - x‖ = ‖x - y‖ := norm_sub_rev _ _
        linarith

  · refine ⟨1, by norm_num, ?_⟩
    intro β s t hst hspan hβi hβ0 hβδ x hx
    exact (hKn ⟨x, hx⟩).elim



/-- The fixed bounded generator obtained by dropping the small Gaussian diffusion and scalar
coefficient term from the first-stage equation. -/
def canonicalTransportLimitGenerator (lam : ℂ) : XG →L[ℂ] XG :=
  ((-2 * Complex.I) • omegaOp) - lam • (1 : XG →L[ℂ] XG)

/-- The inviscid first-stage limit family, the exponential of the actual transport-minus-λ
generator. -/
def canonicalTransportLimitFamily {a b : ℝ} (lam : ℂ) :
    EvolutionFamily XG a b :=
  EvolutionFamily.ofExpSemigroup
    (UnforcedLeray.Infra.ExpSemigroup.ofExp (canonicalTransportLimitGenerator lam)) a b

/-- Duhamel's identity for the concrete bounded-generator limit family. -/
theorem canonicalTransportLimitFamily_mild {a b s t : ℝ} (lam : ℂ)
    (hst : s ≤ t) (x : XG) :
    (canonicalTransportLimitFamily (a := a) (b := b) lam).U t s x =
      x + ∫ r in s..t,
        canonicalTransportLimitGenerator lam
          ((canonicalTransportLimitFamily (a := a) (b := b) lam).U r s x) := by
  let G := canonicalTransportLimitGenerator lam
  have h := Evolution.exp_smul_add_apply_eq_duhamel (0 : XG →L[ℂ] XG) G s t x
  simp only [zero_add, smul_zero, NormedSpace.exp_zero, one_apply_eq_self] at h
  change NormedSpace.exp (((t - s : ℝ) : ℂ) • G) x =
    x + ∫ r in s..t, G (NormedSpace.exp (((r - s : ℝ) : ℂ) • G) x)
  exact h

/-- The bounded-generator orbit on a compact time interval is compact. -/
theorem isCompact_boundedGeneratorOrbit {B : ℝ}
    (G : XG →L[ℂ] XG) (x : XG) :
    IsCompact (Set.range fun u : Set.Icc (0 : ℝ) B =>
      G (NormedSpace.exp ((u.1 : ℂ) • G) x)) := by
  have hc : Continuous fun u : ℝ => G (NormedSpace.exp ((u : ℂ) • G) x) :=
    G.continuous.comp (UnforcedLeray.Infra.continuous_exp_smul_apply G x)
  have hrange : Set.range (fun u : Set.Icc (0 : ℝ) B =>
      G (NormedSpace.exp ((u.1 : ℂ) • G) x)) =
      (fun u : ℝ => G (NormedSpace.exp ((u : ℂ) • G) x)) '' Set.Icc 0 B := by
    ext y
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨u.1, u.2, rfl⟩
    · rintro ⟨u, hu, rfl⟩
      exact ⟨⟨u, hu⟩, rfl⟩
  rw [hrange]
  exact isCompact_Icc.image hc

/-- The free Gaussian perturbation is uniformly close to the identity on the compact
fixed-vector orbit of any bounded generator. -/
theorem exists_delta_freeDiffusion_small_on_boundedGeneratorOrbit
    {B : ℝ} (hB : 0 < B) (G : XG →L[ℂ] XG) (x : XG) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (β : ℝ → ℝ) (s t : ℝ),
      s ≤ t → t - s ≤ B → IntervalIntegrable β volume s t →
      (∀ τ, 0 ≤ β τ) → (∀ τ, β τ ≤ δ) →
      ∀ u ∈ Set.Icc (0 : ℝ) B,
        ‖freeDiffusion β t s (G (NormedSpace.exp ((u : ℂ) • G) x)) -
          G (NormedSpace.exp ((u : ℂ) • G) x)‖ < ε := by
  obtain ⟨δ, hδ, hsmall⟩ := freeDiffusion_uniform_strong_small_on_compact hB
    (isCompact_boundedGeneratorOrbit G x) hε
  refine ⟨δ, hδ, fun β s t hst hspan hβi hβ0 hβδ u hu => ?_⟩
  exact hsmall β s t hst hspan hβi hβ0 hβδ
    (G (NormedSpace.exp ((u : ℂ) • G) x)) ⟨⟨u, hu⟩, rfl⟩



set_option maxHeartbeats 500000 in
/-- The raw mild-equation subtraction identity for the concrete Fβ and bounded-generator limit
family. The next lemma splits its integrand into the diffusion, scalar, and Volterra errors. -/
theorem canonicalTransportDysonFamily_sub_limit_integral {a b s t : ℝ}
    (lam κ : ℂ) (β : ℝ → ℝ) (hβi : ∀ u v, IntervalIntegrable β volume u v)
    (hβ0 : ∀ τ, 0 ≤ β τ) (M : ℝ) (hβM : ∀ τ, |β τ| ≤ M)
    (hβsm : AEStronglyMeasurable β (volume.restrict (Set.Icc a b)))
    (hβblock : ∃ C : ℝ, ∀ r ∈ Set.Icc a b, |β r| ≤ C)
    (hs : a ≤ s) (hst : s ≤ t) (ht : t ≤ b) (x : XG) :
    (canonicalTransportDysonFamily lam κ β hβi hβ0 M hβM hβsm hβblock).U t s x -
      (canonicalTransportLimitFamily (a := a) (b := b) lam).U t s x =
      freeDiffusion β t s x - x +
        ∫ r in s..t,
          freeDiffusion β t r
              ((transportDysonPert ((-2 * Complex.I) • omegaOp) lam κ β a b hβsm hβblock).A r
                ((canonicalTransportDysonFamily lam κ β hβi hβ0 M hβM hβsm hβblock).U r s x)) -
            canonicalTransportLimitGenerator lam
              ((canonicalTransportLimitFamily (a := a) (b := b) lam).U r s x) := by
  let E : EvolutionFamily XG a b := freeDiffusionFamily β hβi hβ0 M hβM
  let A : BoundedPert XG a b :=
    transportDysonPert ((-2 * Complex.I) • omegaOp) lam κ β a b hβsm hβblock
  let F : EvolutionFamily XG a b := canonicalTransportDysonFamily lam κ β hβi hβ0 M hβM hβsm hβblock
  let V : EvolutionFamily XG a b := canonicalTransportLimitFamily (a := a) (b := b) lam
  have hIf : IntervalIntegrable (fun r => E.U t r (A.A r (F.U r s x))) volume s t :=
    E.intervalIntegrable_integrand A hs hst ht
      ((F.continuousOn_fst hs x).mono (Icc_subset_Icc le_rfl ht))
  have hVcont : ContinuousOn (fun r => V.U r s x) (Set.Icc s t) :=
    (V.continuousOn_fst hs x).mono (Icc_subset_Icc le_rfl ht)
  have hcontG : ContinuousOn
      (fun r => canonicalTransportLimitGenerator lam (V.U r s x)) (Set.Icc s t) :=
    (canonicalTransportLimitGenerator lam).continuous.comp_continuousOn hVcont
  have hIg : IntervalIntegrable
      (fun r => canonicalTransportLimitGenerator lam (V.U r s x)) volume s t :=
    hcontG.intervalIntegrable_of_Icc hst
  have hF := Evolution.dyson_left E A ⟨hs, hst, ht⟩ x
  have hV := canonicalTransportLimitFamily_mild (a := a) (b := b) lam hst x
  have hIfD := hIf
  change IntervalIntegrable
      (fun r => E.U t r (A.A r ((dyson E A).U r s x))) volume s t at hIfD
  have hIgV := hIg
  change IntervalIntegrable
      (fun r => canonicalTransportLimitGenerator lam
        ((canonicalTransportLimitFamily (a := a) (b := b) lam).U r s x)) volume s t at hIgV
  change (dyson E A).U t s x - V.U t s x =
    E.U t s x - x +
      ∫ r in s..t, E.U t r (A.A r ((dyson E A).U r s x)) -
        canonicalTransportLimitGenerator lam (V.U r s x)
  rw [hF, hV, intervalIntegral.integral_sub hIfD hIgV]
  exact add_sub_add_comm _ _ _ _



/-- Algebraic three-term splitting of the varying-base mild integrand. -/
theorem clm_mild_integrand_split {E A G : XG →L[ℂ] XG} (u v : XG) :
    E (A u) - G v =
      E (A (u - v)) + (E - 1) (G v) + E ((A - G) v) := by
  simp only [map_sub, sub_apply, one_apply_eq_self]
  module

/-- The concrete Fβ integrand splits into a Volterra term, a compact-orbit diffusion term, and
the small scalar perturbation term. -/
theorem canonicalTransportDyson_integrand_split {a b s r t : ℝ}
    (lam κ : ℂ) (β : ℝ → ℝ) (hβi : ∀ u v, IntervalIntegrable β volume u v)
    (hβ0 : ∀ τ, 0 ≤ β τ) (M : ℝ) (hβM : ∀ τ, |β τ| ≤ M)
    (hβsm : AEStronglyMeasurable β (volume.restrict (Set.Icc a b)))
    (hβblock : ∃ C : ℝ, ∀ u ∈ Set.Icc a b, |β u| ≤ C)
    (hs : a ≤ s) (hsr : s ≤ r) (hrt : r ≤ t) (ht : t ≤ b) (x : XG) :
    freeDiffusion β t r
        ((transportDysonPert ((-2 * Complex.I) • omegaOp) lam κ β a b hβsm hβblock).A r
          ((canonicalTransportDysonFamily lam κ β hβi hβ0 M hβM hβsm hβblock).U r s x)) -
      canonicalTransportLimitGenerator lam
        ((canonicalTransportLimitFamily (a := a) (b := b) lam).U r s x) =
      freeDiffusion β t r
        ((transportDysonPert ((-2 * Complex.I) • omegaOp) lam κ β a b hβsm hβblock).A r
          (((canonicalTransportDysonFamily lam κ β hβi hβ0 M hβM hβsm hβblock).U r s x) -
            ((canonicalTransportLimitFamily (a := a) (b := b) lam).U r s x))) +
        (freeDiffusion β t r - 1)
          (canonicalTransportLimitGenerator lam
            ((canonicalTransportLimitFamily (a := a) (b := b) lam).U r s x)) +
        freeDiffusion β t r
          (((transportDysonPert ((-2 * Complex.I) • omegaOp) lam κ β a b hβsm hβblock).A r -
              canonicalTransportLimitGenerator lam)
            ((canonicalTransportLimitFamily (a := a) (b := b) lam).U r s x)) := by
  exact clm_mild_integrand_split
    (E := freeDiffusion β t r)
    (A := (transportDysonPert ((-2 * Complex.I) • omegaOp) lam κ β a b hβsm hβblock).A r)
    (G := canonicalTransportLimitGenerator lam)
    ((canonicalTransportDysonFamily lam κ β hβi hβ0 M hβM hβsm hβblock).U r s x)
    ((canonicalTransportLimitFamily (a := a) (b := b) lam).U r s x)



/-- Interval-integrated form of the three-term mild-integrand split. All three terms are
integrable by the concrete evolution-family bounds and continuity. -/
theorem canonicalTransportDyson_integral_split {a b s t : ℝ}
    (lam κ : ℂ) (β : ℝ → ℝ) (hβi : ∀ u v, IntervalIntegrable β volume u v)
    (hβ0 : ∀ τ, 0 ≤ β τ) (M : ℝ) (hβM : ∀ τ, |β τ| ≤ M)
    (hβsm : AEStronglyMeasurable β (volume.restrict (Set.Icc a b)))
    (hβblock : ∃ C : ℝ, ∀ u ∈ Set.Icc a b, |β u| ≤ C)
    (hs : a ≤ s) (hst : s ≤ t) (ht : t ≤ b) (x : XG) :
    ∫ r in s..t,
      freeDiffusion β t r
          ((transportDysonPert ((-2 * Complex.I) • omegaOp) lam κ β a b hβsm hβblock).A r
            ((canonicalTransportDysonFamily lam κ β hβi hβ0 M hβM hβsm hβblock).U r s x)) -
        canonicalTransportLimitGenerator lam
          ((canonicalTransportLimitFamily (a := a) (b := b) lam).U r s x)
      =
      (∫ r in s..t,
        freeDiffusion β t r
          ((transportDysonPert ((-2 * Complex.I) • omegaOp) lam κ β a b hβsm hβblock).A r
            (((canonicalTransportDysonFamily lam κ β hβi hβ0 M hβM hβsm hβblock).U r s x) -
              ((canonicalTransportLimitFamily (a := a) (b := b) lam).U r s x)))) +
      (∫ r in s..t,
        (freeDiffusion β t r - 1)
          (canonicalTransportLimitGenerator lam
            ((canonicalTransportLimitFamily (a := a) (b := b) lam).U r s x))) +
      (∫ r in s..t,
        freeDiffusion β t r
          (((transportDysonPert ((-2 * Complex.I) • omegaOp) lam κ β a b hβsm hβblock).A r -
              canonicalTransportLimitGenerator lam)
            ((canonicalTransportLimitFamily (a := a) (b := b) lam).U r s x))) := by
  let E : EvolutionFamily XG a b := freeDiffusionFamily β hβi hβ0 M hβM
  let A : BoundedPert XG a b :=
    transportDysonPert ((-2 * Complex.I) • omegaOp) lam κ β a b hβsm hβblock
  let F : EvolutionFamily XG a b := canonicalTransportDysonFamily lam κ β hβi hβ0 M hβM hβsm hβblock
  let V : EvolutionFamily XG a b := canonicalTransportLimitFamily (a := a) (b := b) lam
  let A₀ : BoundedPert XG a b := BoundedPert.const (canonicalTransportLimitGenerator lam)
  change (∫ r in s..t,
      E.U t r (A.A r (F.U r s x)) - canonicalTransportLimitGenerator lam (V.U r s x)) =
    (∫ r in s..t, E.U t r (A.A r (F.U r s x - V.U r s x))) +
      (∫ r in s..t, (E.U t r - 1) (canonicalTransportLimitGenerator lam (V.U r s x))) +
        (∫ r in s..t, E.U t r ((A.A r - canonicalTransportLimitGenerator lam) (V.U r s x)))
  have hFc : ContinuousOn (fun u => F.U u s x) (Set.Icc s t) :=
    (F.continuousOn_fst hs x).mono (Icc_subset_Icc le_rfl ht)
  have hVc : ContinuousOn (fun u => V.U u s x) (Set.Icc s t) :=
    (V.continuousOn_fst hs x).mono (Icc_subset_Icc le_rfl ht)
  have hdiff : ContinuousOn (fun u => F.U u s x - V.U u s x) (Set.Icc s t) :=
    hFc.sub hVc
  have hI1 : IntervalIntegrable
      (fun r => E.U t r (A.A r (F.U r s x - V.U r s x))) volume s t :=
    E.intervalIntegrable_integrand A hs hst ht hdiff
  have hρ : IntegrableOn
      (fun r => canonicalTransportLimitGenerator lam (V.U r s x)) (Set.Ioc s t) := by
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le hst]
    exact ((canonicalTransportLimitGenerator lam).continuous.comp_continuousOn hVc).intervalIntegrable_of_Icc hst
  have hIEρ : IntervalIntegrable
      (fun r => E.U t r (canonicalTransportLimitGenerator lam (V.U r s x))) volume s t :=
    E.intervalIntegrable_apply hs hst ht hρ
  have hI2 : IntervalIntegrable
      (fun r => (E.U t r - 1) (canonicalTransportLimitGenerator lam (V.U r s x)))
      volume s t := by
    exact hIEρ.sub
      (((canonicalTransportLimitGenerator lam).continuous.comp_continuousOn hVc).intervalIntegrable_of_Icc hst)
  have hI3 : IntervalIntegrable
      (fun r => E.U t r ((A.A r - canonicalTransportLimitGenerator lam) (V.U r s x)))
      volume s t := by
    have h := E.intervalIntegrable_integrand (BoundedPert.sub A A₀) hs hst ht hVc
    simpa [A₀, BoundedPert.sub, BoundedPert.const] using h
  have hsum : IntervalIntegrable
      (fun r =>
        E.U t r (A.A r (F.U r s x - V.U r s x)) +
          ((E.U t r - 1) (canonicalTransportLimitGenerator lam (V.U r s x)) +
            E.U t r ((A.A r - canonicalTransportLimitGenerator lam) (V.U r s x))))
      volume s t := hI1.add (hI2.add hI3)
  calc
    _ = ∫ r in s..t,
        E.U t r (A.A r (F.U r s x - V.U r s x)) +
          ((E.U t r - 1) (canonicalTransportLimitGenerator lam (V.U r s x)) +
            E.U t r ((A.A r - canonicalTransportLimitGenerator lam) (V.U r s x))) := by
          refine intervalIntegral.integral_congr fun r hr => ?_
          have hr' : r ∈ Set.Icc s t := by
            simpa [uIcc_of_le hst] using hr
          simpa only [E, A, F, V, freeDiffusionFamily, freeDiffusion, add_assoc] using
            (canonicalTransportDyson_integrand_split
              lam κ β hβi hβ0 M hβM hβsm hβblock hs hr'.1 hr'.2 ht x)
    _ = ((∫ r in s..t, E.U t r (A.A r (F.U r s x - V.U r s x))) +
          (∫ r in s..t, (E.U t r - 1)
              (canonicalTransportLimitGenerator lam (V.U r s x)))) +
            ∫ r in s..t, E.U t r ((A.A r - canonicalTransportLimitGenerator lam)
              (V.U r s x)) := by
          rw [intervalIntegral.integral_add hI1 (hI2.add hI3),
            intervalIntegral.integral_add hI2 hI3]
          exact (add_assoc _ _ _).symm


/-- The same transport coefficient with a deterministic operator bound. This wrapper keeps the
measurability proof from the concrete coefficient while its norm constant depends only on the
actual envelope `|β| ≤ 1`, not on the witness chosen for `hβblock`. -/
def transportDysonPert_unitBound {a b : ℝ} (T : XG →L[ℂ] XG) (lam κ : ℂ)
    (β : ℝ → ℝ) (hβsm : AEStronglyMeasurable β (volume.restrict (Set.Icc a b)))
    (hβblock : ∃ C : ℝ, ∀ r ∈ Set.Icc a b, |β r| ≤ C)
    (hβ1 : ∀ r, |β r| ≤ 1) : BoundedPert XG a b := by
  let A := transportDysonPert T lam κ β a b hβsm hβblock
  refine ⟨A.A, A.meas, ?_⟩
  refine ⟨‖T‖ + ‖lam‖ + ‖κ‖, fun r hr => ?_⟩
  let I : XG →L[ℂ] XG := 1
  have hβc : ‖(β r : ℂ)‖ ≤ 1 := by
    simpa [Complex.norm_real, Real.norm_eq_abs] using hβ1 r
  have hI : ‖I‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  have hLamNorm : ‖lam • I‖ ≤ ‖lam‖ := by
    rw [norm_smul]
    exact mul_le_of_le_one_right (norm_nonneg lam) hI
  have hκ : ‖((β r : ℂ) * κ) • I‖ ≤ ‖κ‖ := by
    rw [norm_smul, norm_mul]
    calc
      ‖(β r : ℂ)‖ * ‖κ‖ * ‖I‖ ≤ ‖(β r : ℂ)‖ * ‖κ‖ * 1 := by gcongr
      _ = ‖(β r : ℂ)‖ * ‖κ‖ := by ring
      _ ≤ ‖κ‖ := mul_le_of_le_one_left (norm_nonneg κ) hβc
  change ‖T - lam • I - ((β r : ℂ) * κ) • I‖ ≤ _
  calc
    ‖T - lam • I - ((β r : ℂ) * κ) • I‖ ≤
        ‖T - lam • I‖ + ‖((β r : ℂ) * κ) • I‖ := norm_sub_le _ _
    _ ≤ (‖T‖ + ‖lam‖) + ‖κ‖ := by
      have hTL : ‖T - lam • I‖ ≤ ‖T‖ + ‖lam‖ :=
        (norm_sub_le _ _).trans (add_le_add le_rfl hLamNorm)
      exact add_le_add hTL hκ
    _ = ‖T‖ + ‖lam‖ + ‖κ‖ := by ring

@[simp] theorem transportDysonPert_unitBound_A {a b : ℝ} (T : XG →L[ℂ] XG)
    (lam κ : ℂ) (β : ℝ → ℝ)
    (hβsm : AEStronglyMeasurable β (volume.restrict (Set.Icc a b)))
    (hβblock : ∃ C : ℝ, ∀ r ∈ Set.Icc a b, |β r| ≤ C)
    (hβ1 : ∀ r, |β r| ≤ 1) (r : ℝ) :
    (transportDysonPert_unitBound T lam κ β hβsm hβblock hβ1).A r =
      (transportDysonPert T lam κ β a b hβsm hβblock).A r := rfl


/-- The actual Fβ family has a block norm bound independent of the chosen existential β bound,
provided the scalar coefficient obeys `|β| ≤ 1`. -/
theorem canonicalTransportDysonFamily_unitBound_norm_le {a b : ℝ} (lam κ : ℂ)
    (β : ℝ → ℝ) (hβi : ∀ s t, IntervalIntegrable β volume s t)
    (hβ0 : ∀ τ, 0 ≤ β τ) (M : ℝ) (hβM : ∀ τ, |β τ| ≤ M)
    (hβsm : AEStronglyMeasurable β (volume.restrict (Set.Icc a b)))
    (hβblock : ∃ B : ℝ, ∀ t ∈ Set.Icc a b, |β t| ≤ B)
    (hβ1 : ∀ r, |β r| ≤ 1) :
    ∀ s t, a ≤ s → s ≤ t → t ≤ b →
      ‖(canonicalTransportDysonFamily lam κ β hβi hβ0 M hβM hβsm hβblock).U t s‖ ≤
        Real.exp ((‖(-2 * Complex.I) • omegaOp‖ + ‖lam‖ + ‖κ‖) * (t - s)) := by
  let T : XG →L[ℂ] XG := (-2 * Complex.I) • omegaOp
  let E : EvolutionFamily XG a b := freeDiffusionFamily β hβi hβ0 M hβM
  let A : BoundedPert XG a b := transportDysonPert_unitBound T lam κ β hβsm hβblock hβ1
  have hE : ∀ u v, a ≤ u → u ≤ v → v ≤ b → ‖E.U v u‖ ≤ 1 := by
    intro u v hu huv hv
    change ‖freeDiffusion β v u‖ ≤ 1
    exact norm_expD_le _
  have hA : ∀ r ∈ Set.Icc a b, ‖A.A r‖ ≤ ‖T‖ + ‖lam‖ + ‖κ‖ := by
    intro r hr
    let I : XG →L[ℂ] XG := 1
    have hβc : ‖(β r : ℂ)‖ ≤ 1 := by
      simpa [Complex.norm_real, Real.norm_eq_abs] using hβ1 r
    have hI : ‖I‖ ≤ 1 := ContinuousLinearMap.norm_id_le
    have hLamNorm : ‖lam • I‖ ≤ ‖lam‖ := by
      rw [norm_smul]
      exact mul_le_of_le_one_right (norm_nonneg lam) hI
    have hκ : ‖((β r : ℂ) * κ) • I‖ ≤ ‖κ‖ := by
      rw [norm_smul, norm_mul]
      calc
        ‖(β r : ℂ)‖ * ‖κ‖ * ‖I‖ ≤ ‖(β r : ℂ)‖ * ‖κ‖ * 1 := by gcongr
        _ = ‖(β r : ℂ)‖ * ‖κ‖ := by ring
        _ ≤ ‖κ‖ := mul_le_of_le_one_left (norm_nonneg κ) hβc
    change ‖T - lam • I - ((β r : ℂ) * κ) • I‖ ≤ _
    calc
      ‖T - lam • I - ((β r : ℂ) * κ) • I‖ ≤
          ‖T - lam • I‖ + ‖((β r : ℂ) * κ) • I‖ := norm_sub_le _ _
      _ ≤ (‖T‖ + ‖lam‖) + ‖κ‖ := by
        have hTL : ‖T - lam • I‖ ≤ ‖T‖ + ‖lam‖ :=
          (norm_sub_le _ _).trans (add_le_add le_rfl hLamNorm)
        exact add_le_add hTL hκ
      _ = ‖T‖ + ‖lam‖ + ‖κ‖ := by ring
  have hF : ∀ u v, a ≤ u → u ≤ v → v ≤ b →
      ‖E.U v u‖ ≤ 1 * Real.exp (0 * (v - u)) := by
    intro u v hu huv hv
    calc
      ‖E.U v u‖ ≤ 1 := hE u v hu huv hv
      _ = 1 * Real.exp (0 * (v - u)) := by simp
  have hdyson := Evolution.norm_dyson_le (M := 1) (ω := 0)
    (C := ‖T‖ + ‖lam‖ + ‖κ‖) (F := E) (A := A) hF hA
  intro s t hs hst ht
  have hEq :
      (canonicalTransportDysonFamily lam κ β hβi hβ0 M hβM hβsm hβblock).U t s =
        (Evolution.dyson E A).U t s := by
    rfl
  rw [hEq]
  have hbound := hdyson s t hs hst ht
  calc
    ‖(Evolution.dyson E A).U t s‖ ≤
        1 * Real.exp ((0 + 1 * (‖T‖ + ‖lam‖ + ‖κ‖)) * (t - s)) := by
          simpa [E, A] using hbound
    _ = Real.exp ((‖(-2 * Complex.I) • omegaOp‖ + ‖lam‖ + ‖κ‖) * (t - s)) := by
          simp [T]


/-- The first-stage coefficient differs from the inviscid generator only by the scalar `βκ`
term, with a deterministic operator-norm bound. -/
theorem transportDysonPert_sub_generator_norm_le {a b : ℝ} (T : XG →L[ℂ] XG)
    (lam κ : ℂ) (β : ℝ → ℝ)
    (hβsm : AEStronglyMeasurable β (volume.restrict (Set.Icc a b)))
    (hβblock : ∃ C : ℝ, ∀ r ∈ Set.Icc a b, |β r| ≤ C)
    {δ r : ℝ} (hβδ : |β r| ≤ δ) (hδ : 0 ≤ δ)
    (hr : r ∈ Set.Icc a b) :
    ‖(transportDysonPert T lam κ β a b hβsm hβblock).A r -
        (T - lam • (1 : XG →L[ℂ] XG))‖ ≤ δ * ‖κ‖ := by
  let I : XG →L[ℂ] XG := 1
  have hβc : ‖(β r : ℂ)‖ ≤ δ := by
    simpa [Complex.norm_real, Real.norm_eq_abs] using hβδ
  have hI : ‖I‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  change ‖(T - lam • I - ((β r : ℂ) * κ) • I) - (T - lam • I)‖ ≤ _
  have heq : (T - lam • I - ((β r : ℂ) * κ) • I) - (T - lam • I) =
      -(((β r : ℂ) * κ) • I) := by module
  rw [heq, norm_neg, norm_smul, norm_mul]
  calc
    ‖(β r : ℂ)‖ * ‖κ‖ * ‖I‖ ≤ ‖(β r : ℂ)‖ * ‖κ‖ * 1 := by gcongr
    _ = ‖(β r : ℂ)‖ * ‖κ‖ := by ring
    _ ≤ δ * ‖κ‖ := mul_le_mul_of_nonneg_right hβc (norm_nonneg κ)


/-- A direct, deterministic bound for the actual `T−λ−βκ` operator at each point of the block. -/
theorem transportDysonPert_unitBound_pointwise {a b : ℝ} (T : XG →L[ℂ] XG)
    (lam κ : ℂ) (β : ℝ → ℝ)
    (hβsm : AEStronglyMeasurable β (volume.restrict (Set.Icc a b)))
    (hβblock : ∃ C : ℝ, ∀ r ∈ Set.Icc a b, |β r| ≤ C)
    (hβ1 : ∀ r, |β r| ≤ 1) {r : ℝ} (hr : r ∈ Set.Icc a b) :
    ‖(transportDysonPert T lam κ β a b hβsm hβblock).A r‖ ≤ ‖T‖ + ‖lam‖ + ‖κ‖ := by
  let I : XG →L[ℂ] XG := 1
  have hβc : ‖(β r : ℂ)‖ ≤ 1 := by
    simpa [Complex.norm_real, Real.norm_eq_abs] using hβ1 r
  have hI : ‖I‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  have hLamNorm : ‖lam • I‖ ≤ ‖lam‖ := by
    rw [norm_smul]
    exact mul_le_of_le_one_right (norm_nonneg lam) hI
  have hκ : ‖((β r : ℂ) * κ) • I‖ ≤ ‖κ‖ := by
    rw [norm_smul, norm_mul]
    calc
      ‖(β r : ℂ)‖ * ‖κ‖ * ‖I‖ ≤ ‖(β r : ℂ)‖ * ‖κ‖ * 1 := by gcongr
      _ = ‖(β r : ℂ)‖ * ‖κ‖ := by ring
      _ ≤ ‖κ‖ := mul_le_of_le_one_left (norm_nonneg κ) hβc
  change ‖T - lam • I - ((β r : ℂ) * κ) • I‖ ≤ _
  calc
    ‖T - lam • I - ((β r : ℂ) * κ) • I‖ ≤
        ‖T - lam • I‖ + ‖((β r : ℂ) * κ) • I‖ := norm_sub_le _ _
    _ ≤ (‖T‖ + ‖lam‖) + ‖κ‖ := by
      have hTL : ‖T - lam • I‖ ≤ ‖T‖ + ‖lam‖ :=
        (norm_sub_le _ _).trans (add_le_add le_rfl hLamNorm)
      exact add_le_add hTL hκ
    _ = ‖T‖ + ‖lam‖ + ‖κ‖ := by ring

/-- Concrete norm inequality for the varying-base mild subtraction. The two free errors and the
small scalar coefficient are explicit; the remaining term is the Volterra quantity to which
continuous Gronwall applies. -/
theorem canonicalTransportDysonFamily_difference_golden_rule {a b s t : ℝ}
    (lam κ : ℂ) (β : ℝ → ℝ) (hβi : ∀ u v, IntervalIntegrable β volume u v)
    (hβ0 : ∀ τ, 0 ≤ β τ) (M : ℝ) (hβM : ∀ τ, |β τ| ≤ M)
    (hβsm : AEStronglyMeasurable β (volume.restrict (Set.Icc a b)))
    (hβblock : ∃ C : ℝ, ∀ u ∈ Set.Icc a b, |β u| ≤ C)
    (hs : a ≤ s) (hst : s ≤ t) (ht : t ≤ b)
    {δ η η₀ C : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hβδ : ∀ r, |β r| ≤ δ) (hη : 0 ≤ η) (hη₀ : 0 ≤ η₀) (hC : 0 ≤ C)
    (x : XG)
    (hinit : ‖freeDiffusion β t s x - x‖ ≤ η₀)
    (horbit : ∀ r ∈ Set.Icc s t,
      ‖(freeDiffusion β t r - 1)
        (canonicalTransportLimitGenerator lam
          ((canonicalTransportLimitFamily (a := a) (b := b) lam).U r s x))‖ ≤ η)
    (hV : ∀ r ∈ Set.Icc s t,
      ‖(canonicalTransportLimitFamily (a := a) (b := b) lam).U r s x‖ ≤ C) :
    ‖(canonicalTransportDysonFamily lam κ β hβi hβ0 M hβM hβsm hβblock).U t s x -
        (canonicalTransportLimitFamily (a := a) (b := b) lam).U t s x‖ ≤
      η₀ + (t - s) * η + (t - s) * δ * ‖κ‖ * C +
        (‖(-2 * Complex.I) • omegaOp‖ + ‖lam‖ + ‖κ‖) *
          ∫ r in s..t, ‖(canonicalTransportDysonFamily lam κ β hβi hβ0 M hβM hβsm hβblock).U r s x -
            (canonicalTransportLimitFamily (a := a) (b := b) lam).U r s x‖ := by
  let T : XG →L[ℂ] XG := (-2 * Complex.I) • omegaOp
  let G : XG →L[ℂ] XG := canonicalTransportLimitGenerator lam
  let E : EvolutionFamily XG a b := freeDiffusionFamily β hβi hβ0 M hβM
  let A : BoundedPert XG a b :=
    transportDysonPert T lam κ β a b hβsm hβblock
  let F : EvolutionFamily XG a b :=
    canonicalTransportDysonFamily lam κ β hβi hβ0 M hβM hβsm hβblock
  let V : EvolutionFamily XG a b := canonicalTransportLimitFamily (a := a) (b := b) lam
  let A₀ : BoundedPert XG a b := BoundedPert.const G
  have hβ1 : ∀ r, |β r| ≤ 1 := by
    intro r
    calc |β r| ≤ δ := hβδ r
      _ ≤ 1 := hδ1
  have hFc : ContinuousOn (fun r => F.U r s x) (Set.Icc s t) :=
    (F.continuousOn_fst hs x).mono (Icc_subset_Icc le_rfl ht)
  have hVc : ContinuousOn (fun r => V.U r s x) (Set.Icc s t) :=
    (V.continuousOn_fst hs x).mono (Icc_subset_Icc le_rfl ht)
  have hdiffC : ContinuousOn (fun r => F.U r s x - V.U r s x) (Set.Icc s t) :=
    hFc.sub hVc
  have hI1 : IntervalIntegrable
      (fun r => E.U t r (A.A r (F.U r s x - V.U r s x))) volume s t :=
    E.intervalIntegrable_integrand A hs hst ht hdiffC
  have hρ : IntegrableOn (fun r => G (V.U r s x)) (Set.Ioc s t) := by
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le hst]
    exact (G.continuous.comp_continuousOn hVc).intervalIntegrable_of_Icc hst
  have hIEρ : IntervalIntegrable
      (fun r => E.U t r (G (V.U r s x))) volume s t :=
    E.intervalIntegrable_apply hs hst ht hρ
  have hI2 : IntervalIntegrable
      (fun r => (E.U t r - 1) (G (V.U r s x))) volume s t := by
    exact hIEρ.sub ((G.continuous.comp_continuousOn hVc).intervalIntegrable_of_Icc hst)
  have hI3 : IntervalIntegrable
      (fun r => E.U t r ((A.A r - G) (V.U r s x))) volume s t := by
    have h := E.intervalIntegrable_integrand (BoundedPert.sub A A₀) hs hst ht hVc
    simpa [A₀, BoundedPert.sub, BoundedPert.const] using h
  have hsplit := canonicalTransportDyson_integral_split
    lam κ β hβi hβ0 M hβM hβsm hβblock hs hst ht x
  have hsub := canonicalTransportDysonFamily_sub_limit_integral
    lam κ β hβi hβ0 M hβM hβsm hβblock hs hst ht x
  rw [hsplit] at hsub
  have hL : 0 ≤ ‖T‖ + ‖lam‖ + ‖κ‖ := by positivity
  have hVolterra :
      ‖∫ r in s..t, E.U t r (A.A r (F.U r s x - V.U r s x))‖ ≤
        (‖T‖ + ‖lam‖ + ‖κ‖) *
          (∫ r in s..t, ‖F.U r s x - V.U r s x‖) := by
    have hy : IntervalIntegrable (fun r => (‖T‖ + ‖lam‖ + ‖κ‖) * ‖F.U r s x - V.U r s x‖)
        volume s t :=
      ((hdiffC.norm.const_mul (‖T‖ + ‖lam‖ + ‖κ‖)).intervalIntegrable_of_Icc hst)
    refine (intervalIntegral.norm_integral_le_of_norm_le hst
      (ae_of_all _ fun r hr => ?_) hy).trans_eq ?_
    · have hr' : r ∈ Set.Icc s t := ⟨hr.1.le, hr.2⟩
      have hEr : ‖E.U t r‖ ≤ 1 := by
        change ‖freeDiffusion β t r‖ ≤ 1
        exact norm_expD_le _
      have hAr := transportDysonPert_unitBound_pointwise T lam κ β hβsm hβblock hβ1
        ⟨hs.trans hr'.1, hr'.2.trans ht⟩
      calc
        ‖E.U t r (A.A r (F.U r s x - V.U r s x))‖ ≤
            ‖E.U t r‖ * ‖A.A r (F.U r s x - V.U r s x)‖ := (E.U t r).le_opNorm _
        _ ≤ ‖E.U t r‖ * (‖A.A r‖ * ‖F.U r s x - V.U r s x‖) := by
          gcongr
          exact (A.A r).le_opNorm _
        _ ≤ 1 * ((‖T‖ + ‖lam‖ + ‖κ‖) * ‖F.U r s x - V.U r s x‖) := by
          gcongr
        _ = (‖T‖ + ‖lam‖ + ‖κ‖) * ‖F.U r s x - V.U r s x‖ := by ring
    · rw [intervalIntegral.integral_const_mul]
  have hDiffOp : ∀ r ∈ Set.Icc s t, ‖A.A r - G‖ ≤ δ * ‖κ‖ := by
    intro r hr
    exact transportDysonPert_sub_generator_norm_le T lam κ β hβsm hβblock
      (hβδ r) hδ ⟨hs.trans hr.1, hr.2.trans ht⟩
  have hI2bound :
      ‖∫ r in s..t, (E.U t r - 1) (G (V.U r s x))‖ ≤ (t - s) * η := by
    refine (intervalIntegral.norm_integral_le_of_norm_le
      (g := fun _ : ℝ => η) hst
      (ae_of_all _ fun r hr => ?_)
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => η) volume s t)).trans_eq ?_
    · have hr' : r ∈ Set.Icc s t := ⟨hr.1.le, hr.2⟩
      exact horbit r hr'
    · rw [intervalIntegral.integral_const, smul_eq_mul]
  have hI3bound :
      ‖∫ r in s..t, E.U t r ((A.A r - G) (V.U r s x))‖ ≤
        (t - s) * δ * ‖κ‖ * C := by
    refine (intervalIntegral.norm_integral_le_of_norm_le
      (g := fun _ : ℝ => δ * ‖κ‖ * C) hst
      (ae_of_all _ fun r hr => ?_)
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => δ * ‖κ‖ * C) volume s t)).trans_eq ?_
    · have hr' : r ∈ Set.Icc s t := ⟨hr.1.le, hr.2⟩
      have hEr : ‖E.U t r‖ ≤ 1 := by
        change ‖freeDiffusion β t r‖ ≤ 1
        exact norm_expD_le _
      have hVx := hV r hr'
      have hDiff := hDiffOp r hr'
      calc
        ‖E.U t r ((A.A r - G) (V.U r s x))‖ ≤
            ‖E.U t r‖ * ‖(A.A r - G) (V.U r s x)‖ := (E.U t r).le_opNorm _
        _ ≤ ‖E.U t r‖ * (‖A.A r - G‖ * ‖V.U r s x‖) := by
          gcongr
          exact (A.A r - G).le_opNorm _
        _ ≤ 1 * (δ * ‖κ‖ * C) := by
          gcongr
        _ = δ * ‖κ‖ * C := by ring
    · rw [intervalIntegral.integral_const, smul_eq_mul]
      ring
  have hfinal := norm_add_le
    (freeDiffusion β t s x - x)
    (((∫ r in s..t, E.U t r (A.A r (F.U r s x - V.U r s x))) +
      ∫ r in s..t, (E.U t r - 1) (G (V.U r s x))) +
        ∫ r in s..t, E.U t r ((A.A r - G) (V.U r s x)))
  have hsum := norm_add_le
    (∫ r in s..t, E.U t r (A.A r (F.U r s x - V.U r s x)))
    ((∫ r in s..t, (E.U t r - 1) (G (V.U r s x))) +
      ∫ r in s..t, E.U t r ((A.A r - G) (V.U r s x)))
  have hsum' := norm_add_le
    (∫ r in s..t, (E.U t r - 1) (G (V.U r s x)))
    (∫ r in s..t, E.U t r ((A.A r - G) (V.U r s x)))
  have hsubLocal : F.U t s x - V.U t s x =
      (freeDiffusion β t s x - x) +
        (((∫ r in s..t, E.U t r (A.A r (F.U r s x - V.U r s x))) +
          ∫ r in s..t, (E.U t r - 1) (G (V.U r s x))) +
            ∫ r in s..t, E.U t r ((A.A r - G) (V.U r s x))) := by
    exact hsub
  have hsumBig := norm_add_le
    ((∫ r in s..t, E.U t r (A.A r (F.U r s x - V.U r s x))) +
      ∫ r in s..t, (E.U t r - 1) (G (V.U r s x)))
    (∫ r in s..t, E.U t r ((A.A r - G) (V.U r s x)))
  have hnorm : ‖F.U t s x - V.U t s x‖ ≤
      η₀ + (t - s) * η + (t - s) * δ * ‖κ‖ * C +
        (‖T‖ + ‖lam‖ + ‖κ‖) *
          (∫ r in s..t, ‖F.U r s x - V.U r s x‖) := by
    rw [hsubLocal]
    calc
      ‖(freeDiffusion β t s x - x) +
          (((∫ r in s..t, E.U t r (A.A r (F.U r s x - V.U r s x))) +
            ∫ r in s..t, (E.U t r - 1) (G (V.U r s x))) +
              ∫ r in s..t, E.U t r ((A.A r - G) (V.U r s x)))‖ ≤
        ‖freeDiffusion β t s x - x‖ +
          ‖((∫ r in s..t, E.U t r (A.A r (F.U r s x - V.U r s x))) +
            ∫ r in s..t, (E.U t r - 1) (G (V.U r s x))) +
              ∫ r in s..t, E.U t r ((A.A r - G) (V.U r s x))‖ := norm_add_le _ _
      _ ≤ ‖freeDiffusion β t s x - x‖ +
          ‖∫ r in s..t, E.U t r (A.A r (F.U r s x - V.U r s x))‖ +
            ‖∫ r in s..t, (E.U t r - 1) (G (V.U r s x))‖ +
              ‖∫ r in s..t, E.U t r ((A.A r - G) (V.U r s x))‖ := by
        have hsum' := norm_add_le
          (∫ r in s..t, E.U t r (A.A r (F.U r s x - V.U r s x)))
          (∫ r in s..t, (E.U t r - 1) (G (V.U r s x)))
        have hsum'' := norm_add_le
          ((∫ r in s..t, E.U t r (A.A r (F.U r s x - V.U r s x))) +
            ∫ r in s..t, (E.U t r - 1) (G (V.U r s x)))
          (∫ r in s..t, E.U t r ((A.A r - G) (V.U r s x)))
        linarith
      _ ≤ η₀ + (‖T‖ + ‖lam‖ + ‖κ‖) *
          (∫ r in s..t, ‖F.U r s x - V.U r s x‖) +
          (t - s) * η + (t - s) * δ * ‖κ‖ * C := by
        have hp1 := add_le_add hinit hVolterra
        have hp2 := add_le_add hI2bound hI3bound
        calc
          _ = (‖freeDiffusion β t s x - x‖ +
                ‖∫ r in s..t, E.U t r (A.A r (F.U r s x - V.U r s x))‖) +
                (‖∫ r in s..t, (E.U t r - 1) (G (V.U r s x))‖ +
                  ‖∫ r in s..t, E.U t r ((A.A r - G) (V.U r s x))‖) := by ring
          _ ≤ (η₀ + (‖T‖ + ‖lam‖ + ‖κ‖) *
                (∫ r in s..t, ‖F.U r s x - V.U r s x‖)) +
                ((t - s) * η + (t - s) * δ * ‖κ‖ * C) := add_le_add hp1 hp2
          _ = η₀ + (‖T‖ + ‖lam‖ + ‖κ‖) *
                (∫ r in s..t, ‖F.U r s x - V.U r s x‖) +
                (t - s) * η + (t - s) * δ * ‖κ‖ * C := by ring_nf
      _ = η₀ + (t - s) * η + (t - s) * δ * ‖κ‖ * C +
          (‖T‖ + ‖lam‖ + ‖κ‖) *
            (∫ r in s..t, ‖F.U r s x - V.U r s x‖) := by ring_nf
  simpa only [F, V] using hnorm


set_option maxHeartbeats 500000 in
/-- Gronwall closure of the concrete varying-base mild inequality on a fixed block. The hypotheses
on the free errors are uniform over every intermediate endpoint, as supplied by the compact-orbit
strong-smallness lemmas. -/
theorem canonicalTransportDysonFamily_difference_gronwall {a b s t : ℝ}
    (lam κ : ℂ) (β : ℝ → ℝ) (hβi : ∀ u v, IntervalIntegrable β volume u v)
    (hβ0 : ∀ τ, 0 ≤ β τ) (M : ℝ) (hβM : ∀ τ, |β τ| ≤ M)
    (hβsm : AEStronglyMeasurable β (volume.restrict (Set.Icc a b)))
    (hβblock : ∃ C : ℝ, ∀ u ∈ Set.Icc a b, |β u| ≤ C)
    (hs : a ≤ s) (hst : s ≤ t) (ht : t ≤ b)
    {B δ η η₀ C : ℝ} (hB : 0 < B) (hspan : t - s ≤ B)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hβδ : ∀ r, |β r| ≤ δ)
    (hη : 0 ≤ η) (hη₀ : 0 ≤ η₀) (hC : 0 ≤ C)
    (x : XG)
    (hinit : ∀ u, s ≤ u → u ≤ t →
      ‖freeDiffusion β u s x - x‖ ≤ η₀)
    (horbit : ∀ u, s ≤ u → u ≤ t → ∀ r, s ≤ r → r ≤ u →
      ‖(freeDiffusion β u r - 1)
        (canonicalTransportLimitGenerator lam
          ((canonicalTransportLimitFamily (a := a) (b := b) lam).U r s x))‖ ≤ η)
    (hVbound : ∀ u, s ≤ u → u ≤ t → ∀ r, s ≤ r → r ≤ u →
      ‖(canonicalTransportLimitFamily (a := a) (b := b) lam).U r s x‖ ≤ C) :
    ‖(canonicalTransportDysonFamily lam κ β hβi hβ0 M hβM hβsm hβblock).U t s x -
        (canonicalTransportLimitFamily (a := a) (b := b) lam).U t s x‖ ≤
      (η₀ + B * η + B * δ * ‖κ‖ * C) *
        Real.exp ((‖(-2 * Complex.I) • omegaOp‖ + ‖lam‖ + ‖κ‖) * (t - s)) := by
  let F := canonicalTransportDysonFamily lam κ β hβi hβ0 M hβM hβsm hβblock
  let V := canonicalTransportLimitFamily (a := a) (b := b) lam
  let L : ℝ := ‖(-2 * Complex.I) • omegaOp‖ + ‖lam‖ + ‖κ‖
  let A : ℝ := η₀ + B * η + B * δ * ‖κ‖ * C
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hAc : 0 ≤ A := by dsimp [A]; positivity
  have hFc : ContinuousOn (fun r => F.U r s x) (Set.Icc s t) :=
    (F.continuousOn_fst hs x).mono (Icc_subset_Icc le_rfl ht)
  have hVc : ContinuousOn (fun r => V.U r s x) (Set.Icc s t) :=
    (V.continuousOn_fst hs x).mono (Icc_subset_Icc le_rfl ht)
  have hy : ContinuousOn (fun r => ‖F.U r s x - V.U r s x‖) (Set.Icc s t) :=
    continuous_norm.comp_continuousOn (hFc.sub hVc)
  have hineq : ∀ u ∈ Set.Icc s t,
      ‖F.U u s x - V.U u s x‖ ≤ A + ∫ r in s..u, L * ‖F.U r s x - V.U r s x‖ := by
    intro u hu
    have hgold := canonicalTransportDysonFamily_difference_golden_rule
      lam κ β hβi hβ0 M hβM hβsm hβblock hs hu.1 (le_trans hu.2 ht)
      hδ hδ1 hβδ hη hη₀ hC x
      (hinit u hu.1 hu.2)
      (fun r hr => horbit u hu.1 hu.2 r hr.1 hr.2)
      (fun r hr => hVbound u hu.1 hu.2 r hr.1 hr.2)
    have hlen : u - s ≤ B := (sub_le_sub_right hu.2 s).trans hspan
    have htime : (u - s) * η + (u - s) * δ * ‖κ‖ * C ≤
        B * η + B * δ * ‖κ‖ * C := by
      have hηpart := mul_le_mul_of_nonneg_right hlen hη
      have hpert := mul_le_mul_of_nonneg_right hlen
        (show 0 ≤ δ * ‖κ‖ * C by positivity)
      nlinarith
    have hInt : L * (∫ r in s..u, ‖F.U r s x - V.U r s x‖) =
        ∫ r in s..u, L * ‖F.U r s x - V.U r s x‖ := by
      rw [← intervalIntegral.integral_const_mul]
    change ‖F.U u s x - V.U u s x‖ ≤
      η₀ + (u - s) * η + (u - s) * δ * ‖κ‖ * C +
        L * (∫ r in s..u, ‖F.U r s x - V.U r s x‖) at hgold
    rw [hInt] at hgold
    calc
      ‖F.U u s x - V.U u s x‖ ≤
          η₀ + (u - s) * η + (u - s) * δ * ‖κ‖ * C +
            ∫ r in s..u, L * ‖F.U r s x - V.U r s x‖ := hgold
      _ ≤ A + ∫ r in s..u, L * ‖F.U r s x - V.U r s x‖ := by
        dsimp [A]
        linarith
  have hG := UnforcedLeray.Gronwall.le_exp_of_integral_le
    (y := fun r => ‖F.U r s x - V.U r s x‖)
    (β := fun _ => L) (A := A) (s := s) (T := t)
    hy continuousOn_const (fun _ _ => hL) hineq
  have hresult := hG t ⟨hst, le_rfl⟩
  have hnormT : ‖(-2 * Complex.I) • omegaOp‖ = ‖(2 * Complex.I) • omegaOp‖ := by
    rw [show (-2 * Complex.I : ℂ) = -(2 * Complex.I) by ring, neg_smul, norm_neg]
  have hresult' : ‖F.U t s x - V.U t s x‖ ≤
      A * Real.exp ((t - s) * ‖(2 * Complex.I) • omegaOp‖ +
        (t - s) * ‖lam‖ + (t - s) * ‖κ‖) := by
    simpa [F, V, A, L, intervalIntegral.integral_const, smul_eq_mul, mul_add, add_mul] using hresult
  calc
    ‖(canonicalTransportDysonFamily lam κ β hβi hβ0 M hβM hβsm hβblock).U t s x -
        (canonicalTransportLimitFamily (a := a) (b := b) lam).U t s x‖ ≤
        A * Real.exp ((t - s) * ‖(2 * Complex.I) • omegaOp‖ +
          (t - s) * ‖lam‖ + (t - s) * ‖κ‖) := by simpa [F, V] using hresult'
    _ = (η₀ + B * η + B * δ * ‖κ‖ * C) *
        Real.exp ((‖(-2 * Complex.I) • omegaOp‖ + ‖lam‖ + ‖κ‖) * (t - s)) := by
      rw [hnormT]
      dsimp [A]
      congr 1
      ring


/-- Explicit norm bound for the inviscid bounded-generator orbit on a block of length B. This
constant depends only on the duration and generator, not on the containing interval or its chosen
family-bound witness. -/
theorem canonicalTransportLimitFamily_apply_norm_le {a b s t B : ℝ} (lam : ℂ)
    (hs : a ≤ s) (hst : s ≤ t) (ht : t ≤ b) (hspan : t - s ≤ B) (x : XG) :
    ‖(canonicalTransportLimitFamily (a := a) (b := b) lam).U t s x‖ ≤
      Real.exp (‖canonicalTransportLimitGenerator lam‖ * B) * ‖x‖ := by
  let G := canonicalTransportLimitGenerator lam
  let V := canonicalTransportLimitFamily (a := a) (b := b) lam
  have hformula : V.U t s x = NormedSpace.exp (((t - s : ℝ) : ℂ) • G) x := by
    simp [V, G, canonicalTransportLimitFamily,
      UnforcedLeray.Evolution.EvolutionFamily.ofExpSemigroup_U,
      UnforcedLeray.Infra.ExpSemigroup.ofExp_T]
  have htime : 0 ≤ t - s := sub_nonneg.mpr hst
  have hB : 0 ≤ B := hspan.trans' htime
  calc
    ‖V.U t s x‖ = ‖NormedSpace.exp (((t - s : ℝ) : ℂ) • G) x‖ := by rw [hformula]
    _ ≤ ‖NormedSpace.exp (((t - s : ℝ) : ℂ) • G)‖ * ‖x‖ :=
      (NormedSpace.exp (((t - s : ℝ) : ℂ) • G)).le_opNorm x
    _ ≤ Real.exp (|t - s| * ‖G‖) * ‖x‖ := by
      exact mul_le_mul_of_nonneg_right (UnforcedLeray.Infra.BanachExp.norm_exp_smul_le G (t - s)) (norm_nonneg _)
    _ = Real.exp ((t - s) * ‖G‖) * ‖x‖ := by rw [abs_of_nonneg htime]
    _ ≤ Real.exp (B * ‖G‖) * ‖x‖ := by
      gcongr
    _ = Real.exp (‖G‖ * B) * ‖x‖ := by congr 2 <;> ring

set_option maxHeartbeats 600000 in
/-- Actual uniform strong convergence of the concrete first Dyson stage to its inviscid
transport-minus-λ evolution, as the nonnegative Gaussian coefficient tends uniformly to zero on
a fixed-duration window. The threshold is independent of the location of the window. -/
theorem exists_delta_canonicalTransportDysonFamily_uniform_strong_small {a b B : ℝ}
    (hB : 0 < B) (lam κ : ℂ) (x : XG) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (β : ℝ → ℝ)
      (hβi : ∀ u v, IntervalIntegrable β volume u v)
      (hβ0 : ∀ τ, 0 ≤ β τ)
      (hβsm : AEStronglyMeasurable β (volume.restrict (Set.Icc a b)))
      (hβM : ∀ r, |β r| ≤ δ) (s t : ℝ),
      a ≤ s → s ≤ t → t ≤ b → t - s ≤ B →
      ‖(canonicalTransportDysonFamily lam κ β hβi hβ0 δ hβM hβsm
        (⟨δ, fun r _ => hβM r⟩ : ∃ C₀ : ℝ, ∀ r ∈ Set.Icc a b, |β r| ≤ C₀)).U t s x -
          (canonicalTransportLimitFamily (a := a) (b := b) lam).U t s x‖ < ε := by
  let G := canonicalTransportLimitGenerator lam
  let L : ℝ := ‖(-2 * Complex.I) • omegaOp‖ + ‖lam‖ + ‖κ‖
  let C : ℝ := Real.exp (‖G‖ * B) * ‖x‖
  let R : ℝ := Real.exp (L * B)
  let ρ : ℝ := ε / (2 * R)
  let η₀ : ℝ := ρ / 2
  let η : ℝ := ρ / (4 * B)
  let δp : ℝ := ρ / (4 * B * (‖κ‖ * C + 1))
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hR : 0 < R := Real.exp_pos _
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hη₀ : 0 < η₀ := by dsimp [η₀]; positivity
  have hη : 0 < η := by dsimp [η]; positivity
  have hδp : 0 < δp := by dsimp [δp]; positivity
  obtain ⟨δi, hδi, hsmalli⟩ := freeDiffusion_uniform_strong_small_on_compact hB
    (isCompact_singleton : IsCompact ({x} : Set XG)) hη₀
  obtain ⟨δo, hδo, hsmallo⟩ :=
    exists_delta_freeDiffusion_small_on_boundedGeneratorOrbit hB G x hη
  let δ := min δi (min δo (min δp 1))
  have hδ : 0 < δ := by
    dsimp [δ]
    exact lt_min hδi (lt_min hδo (lt_min hδp zero_lt_one))
  have hδi' : δ ≤ δi := by dsimp [δ]; exact min_le_left _ _
  have hδo' : δ ≤ δo := by
    dsimp [δ]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hδp' : δ ≤ δp := by
    dsimp [δ]; exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hδ1 : δ ≤ 1 := by
    dsimp [δ]; exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  refine ⟨δ, hδ, ?_⟩
  intro β hβi hβ0 hβsm hβM s t hs hst ht hspan
  have hβδi : ∀ r, β r ≤ δi := fun r => (le_abs_self (β r)).trans (hβM r) |>.trans hδi'
  have hβδo : ∀ r, β r ≤ δo := fun r => (le_abs_self (β r)).trans (hβM r) |>.trans hδo'
  have hβblock : ∃ C₀ : ℝ, ∀ r ∈ Set.Icc a b, |β r| ≤ C₀ :=
    ⟨δ, fun r _ => hβM r⟩
  let F := canonicalTransportDysonFamily lam κ β hβi hβ0 δ hβM hβsm hβblock
  let V := canonicalTransportLimitFamily (a := a) (b := b) lam
  have hinit : ∀ u, s ≤ u → u ≤ t → ‖freeDiffusion β u s x - x‖ ≤ η₀ := by
    intro u hsu hut
    have hspanu : u - s ≤ B := (sub_le_sub_right hut s).trans hspan
    have hsmall := hsmalli β s u hsu hspanu (hβi s u) hβ0 hβδi x (Set.mem_singleton x)
    exact hsmall.le
  have horbit : ∀ u, s ≤ u → u ≤ t → ∀ r, s ≤ r → r ≤ u →
      ‖(freeDiffusion β u r - 1) (G (V.U r s x))‖ ≤ η := by
    intro u hsu hut r hsr hru
    have hspanu : u - s ≤ B := (sub_le_sub_right hut s).trans hspan
    have hspanur : u - r ≤ B := by linarith
    have hspanr : r - s ≤ B := by linarith
    have hu' : r - s ∈ Set.Icc (0 : ℝ) B := ⟨sub_nonneg.mpr hsr, hspanr⟩
    have hsmall := hsmallo β r u hru hspanur (hβi r u) hβ0 hβδo (r - s) hu'
    have hrepr : V.U r s x = NormedSpace.exp (((r - s : ℝ) : ℂ) • G) x := by
      simp [V, G, canonicalTransportLimitFamily,
      UnforcedLeray.Evolution.EvolutionFamily.ofExpSemigroup_U,
      UnforcedLeray.Infra.ExpSemigroup.ofExp_T]
    simpa [ContinuousLinearMap.sub_apply, hrepr] using hsmall.le
  have hVbound : ∀ u, s ≤ u → u ≤ t → ∀ r, s ≤ r → r ≤ u → ‖V.U r s x‖ ≤ C := by
    intro u hsu hut r hsr hru
    have hspanr : r - s ≤ B := by linarith
    have h := canonicalTransportLimitFamily_apply_norm_le lam hs hsr (le_trans hru (le_trans hut ht)) hspanr x
    simpa [C, G] using h
  have hGron := canonicalTransportDysonFamily_difference_gronwall
    lam κ β hβi hβ0 δ hβM hβsm hβblock hs hst ht
    hB hspan (le_of_lt hδ) hδ1 hβM (le_of_lt hη) (le_of_lt hη₀) hC x
    hinit horbit hVbound
  have hηB : B * η = ρ / 4 := by
    dsimp [η]
    field_simp
  have hκC : 0 ≤ ‖κ‖ * C := mul_nonneg (norm_nonneg _) hC
  have hpert : B * δ * ‖κ‖ * C ≤ ρ / 4 := by
    have hδterm : B * δ * (‖κ‖ * C) ≤ B * δp * (‖κ‖ * C) := by
      calc
        B * δ * (‖κ‖ * C) = B * (δ * (‖κ‖ * C)) := by ring
        _ ≤ B * (δp * (‖κ‖ * C)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hδp' hκC) hB.le
        _ = B * δp * (‖κ‖ * C) := by ring
    have hratio : B * δp * (‖κ‖ * C) ≤ ρ / 4 := by
      dsimp [δp]
      have hden : 4 * B * (‖κ‖ * C + 1) ≠ 0 := by positivity
      field_simp
      nlinarith [hρ, hB, hκC]
    calc
      B * δ * ‖κ‖ * C = B * δ * (‖κ‖ * C) := by ring
      _ ≤ B * δp * (‖κ‖ * C) := hδterm
      _ ≤ ρ / 4 := hratio
  have hA : η₀ + B * η + B * δ * ‖κ‖ * C ≤ ρ := by
    dsimp [η₀]
    rw [hηB]
    linarith
  have hExp : Real.exp (L * (t - s)) ≤ R := by
    dsimp [R]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hspan hL)
  have hbound : ‖F.U t s x - V.U t s x‖ ≤ ρ * R := by
    calc
      ‖F.U t s x - V.U t s x‖ ≤
          (η₀ + B * η + B * δ * ‖κ‖ * C) * Real.exp (L * (t - s)) := by
            simpa [F, V, L] using hGron
      _ ≤ ρ * R := by
        calc
          (η₀ + B * η + B * δ * ‖κ‖ * C) * Real.exp (L * (t - s)) ≤
              ρ * Real.exp (L * (t - s)) :=
                mul_le_mul_of_nonneg_right hA (Real.exp_pos _).le
          _ ≤ ρ * R := mul_le_mul_of_nonneg_left hExp hρ.le
  have hρR : ρ * R = ε / 2 := by dsimp [ρ]; field_simp
  rw [hρR] at hbound
  have hFinal : ‖F.U t s x - V.U t s x‖ < ε := by linarith
  simpa [F, V] using hFinal


end UnforcedLeray.Cons.G3b
