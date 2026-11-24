import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T20
import UnforcedLeray.Short.PartIIa.Tasks.R01EarlyBound
import UnforcedLeray.Short.PartIIa.Tasks.R02LateTable
import UnforcedLeray.Short.PartI.Tasks.TrainHeatFixed.JointFromAgeJets
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.InletSourcePtw.Fields.RawJointSmooth.RawParityForm.RingProfileJet
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.InletProfileJets.RingStreamJets
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.RawJet.Leaves.VelTail
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.RawJet.Leaves.TrainChartBridge

/-!
# `PartII-b:T20/1` (`FlatKObsOpPackage`): smooth observation-operator package for `ϑ • flatK`

Source of record: `the November 2 reference manuscript`, lines 2007–2023.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete
open UnforcedLeray.Short.PartI (ageJet wSupNorm polyPS trainPeriod)
open UnforcedLeray.Train (jap)

/-! ## 1. Unconditional weighted jet bounds for the train velocity -/

private theorem trainWeightedJetBounds_uncond : UnforcedLeray.Short.PartI.TrainWeightedJetBounds := by
  have hOFluct : UnforcedLeray.Short.PartI.OverlapFluctuationDecay :=
    UnforcedLeray.Short.PartI.overlap_fluctuation_decay
      UnforcedLeray.Short.PartI.overlap_highnorm_uniform
  have hOMean : UnforcedLeray.Short.PartI.OverlapMeanDecay :=
    UnforcedLeray.Short.PartI.overlap_mean_decay
      UnforcedLeray.Short.PartI.overlap_highnorm_uniform hOFluct
      UnforcedLeray.Short.PartI.overlap_mean_primitive
  have hOv : UnforcedLeray.Short.PartI.TrainOverlap :=
    UnforcedLeray.Short.PartI.trainOverlap_proof hOFluct hOMean
  have hVort : UnforcedLeray.Short.PartI.TrainVorticityGaussianTail :=
    UnforcedLeray.Short.PartI.train_vorticity_gaussian_tail hOv
  exact UnforcedLeray.Short.PartI.trainWeightedJetBounds_proof hOv hVort
    (UnforcedLeray.Short.PartI.trainStreamVelocityPressureTransverseTail_proof hOv hVort)

private theorem pt_of_wSupNorm_zero {E : Type*} [NormedAddCommGroup E] (f : UnforcedLeray.Cyl.Plane → E)
    {K : ℝ} (hK : 0 ≤ K) (h : wSupNorm 0 f ≤ ENNReal.ofReal K) (z : UnforcedLeray.Cyl.Plane) :
    ‖f z‖ ≤ K := by
  have h1 := UnforcedLeray.Short.PartIIa.lmc_pt_of_sup 0 f hK h z
  have hj : jap 0 z = 1 := by simp [jap]
  rw [hj, one_mul] at h1
  nlinarith [norm_nonneg (f z)]

private theorem polyPS_le_gamma_pow {C : ℝ} (hC : 0 ≤ C) (N : ℕ) {ν s Γ : ℝ}
    (hν : 0 < ν) (hΓ1 : 1 ≤ Γ) (hνi : ν⁻¹ ≤ Γ) (hs0 : 0 < s) (hsΓ : s ≤ Γ) :
    polyPS C N ν (trainPeriod 2 ν) s ≤ (C * 6 ^ N) * Γ ^ (3 * N) := by
  have hΓ0 : 0 ≤ Γ := zero_le_one.trans hΓ1
  have hc : trainPeriod 2 ν = (ν⁻¹) ^ 2 := by
    rw [velTail_trainPeriod_two hν, inv_pow]
  have hc_le : trainPeriod 2 ν ≤ Γ ^ 2 := by
    rw [hc]
    exact pow_le_pow_left₀ (inv_nonneg.mpr hν.le) hνi 2
  have hνi_le : ν⁻¹ ≤ Γ ^ 2 := by nlinarith
  have h1_le : (1 : ℝ) ≤ Γ ^ 2 := by nlinarith
  have hA : 1 + trainPeriod 2 ν + ν⁻¹ ≤ 3 * Γ ^ 2 := by linarith
  have hB : 1 + s ≤ 2 * Γ := by linarith
  have hAB : (1 + trainPeriod 2 ν + ν⁻¹) * (1 + s) ≤ 6 * Γ ^ 3 := by
    calc (1 + trainPeriod 2 ν + ν⁻¹) * (1 + s)
        ≤ (3 * Γ ^ 2) * (2 * Γ) :=
          mul_le_mul hA hB (by linarith) (by positivity)
      _ = 6 * Γ ^ 3 := by ring
  have hAB0 : 0 ≤ (1 + trainPeriod 2 ν + ν⁻¹) * (1 + s) := by
    have : 0 ≤ trainPeriod 2 ν := by rw [hc]; positivity
    positivity
  unfold polyPS
  calc C * ((1 + trainPeriod 2 ν + ν⁻¹) * (1 + s)) ^ N
      ≤ C * (6 * Γ ^ 3) ^ N :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hAB0 hAB N) hC
    _ = (C * 6 ^ N) * Γ ^ (3 * N) := by
        rw [mul_pow, ← pow_mul]
        ring

/-- Uniform bound on `‖iteratedFDeriv ℝ i (fun y : Coord => p.train.v y.1 y.2 idx) x‖` for `i ≤ 9`
and `0 < x.1 ≤ Γ`. -/
private theorem train_vel_coord_jet_bound :
    ∃ (N_v : ℕ) (C_v ν₀ : ℝ), 0 < C_v ∧ 0 < ν₀ ∧
      ∀ (p : Params) (d dm dp : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ →
      ∀ Γ : ℝ, 1 ≤ Γ → p.ν⁻¹ ≤ Γ →
      ∀ (idx : Fin 2) (i : ℕ), i ≤ 9 → ∀ x : Coord, 0 < x.1 → x.1 ≤ Γ →
        ‖iteratedFDeriv ℝ i (fun y : Coord => p.train.v y.1 y.2 idx) x‖ ≤ C_v * Γ ^ N_v := by
  have hW := trainWeightedJetBounds_uncond
  choose C_p N_p ν_p hC_p hν_p hB_p using
    fun q : ℕ × ℕ => hW 2 (by norm_num) 0 q.1 q.2
  obtain ⟨S, hS_def⟩ : ∃ S : Finset (ℕ × ℕ), S = Finset.range 10 ×ˢ Finset.range 10 := ⟨_, rfl⟩
  have hSne : S.Nonempty := ⟨(0, 0), by
    rw [hS_def]
    exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩⟩
  obtain ⟨ν₀, hν₀_def⟩ : ∃ ν₀ : ℝ, ν₀ = S.inf' hSne ν_p := ⟨_, rfl⟩
  have hν₀ : 0 < ν₀ := by
    rw [hν₀_def]
    exact (Finset.lt_inf'_iff hSne).2 fun q _ => hν_p q
  obtain ⟨N_max, hN_max_def⟩ : ∃ N_max : ℕ, N_max = S.sup N_p := ⟨_, rfl⟩
  obtain ⟨C_max, hC_max_def⟩ :
      ∃ C_max : ℝ, C_max = 1 + ∑ q ∈ S, C_p q * (6 : ℝ) ^ (N_p q) := ⟨_, rfl⟩
  have hC_max : 0 < C_max := by
    have : 0 ≤ ∑ q ∈ S, C_p q * (6 : ℝ) ^ (N_p q) :=
      Finset.sum_nonneg fun q _ => mul_nonneg (hC_p q).le (by positivity)
    linarith [hC_max_def]
  refine ⟨3 * N_max, 10 * (3 : ℝ) ^ 9 * C_max, ν₀, by positivity, hν₀, ?_⟩
  intro p d dm dp hBG hνle Γ hΓ1 hνi idx i hi x hx0 hxΓ
  have hνpos : 0 < p.ν := p.ν_pos
  have hc_eq : p.c = trainPeriod 2 p.ν := hBG.c_eq.trans (velTail_trainPeriod_two hνpos).symm
  obtain ⟨tr', htr'_buc, htr'_v⟩ := velTail_transport hc_eq p.train hBG.train_buc
  have hG : ContDiffOn ℝ ∞ (fun y : Coord => p.train.v y.1 y.2) (Ioi 0 ×ˢ univ) :=
    p.train.isTrain.smooth_v.mono (Set.prod_mono Set.Ioi_subset_Ici_self Subset.rfl)
  have hF : ContDiffOn ℝ ∞ (fun y : Coord => p.train.v y.1 y.2 idx) (Ioi 0 ×ˢ univ) :=
    (EuclideanSpace.proj idx : UnforcedLeray.Train.Vec →L[ℝ] ℝ).contDiff.comp_contDiffOn hG
  have hage : ∀ ℓ ∈ Finset.range (i + 1),
      ‖ageJet ℓ (i - ℓ) (fun r z => p.train.v r z idx) x.1 x.2‖ ≤ C_max * Γ ^ (3 * N_max) := by
    intro ℓ hℓ
    have hℓ_lt : ℓ < 10 := by rw [Finset.mem_range] at hℓ; omega
    have hj_lt : i - ℓ < 10 := by omega
    have hqS : (ℓ, i - ℓ) ∈ S := by
      rw [hS_def]
      exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr hℓ_lt, Finset.mem_range.mpr hj_lt⟩
    have hνq : p.ν ≤ ν_p (ℓ, i - ℓ) := by
      have : ν₀ ≤ ν_p (ℓ, i - ℓ) := by rw [hν₀_def]; exact Finset.inf'_le ν_p hqS
      exact hνle.trans this
    have hsup := (hB_p (ℓ, i - ℓ) p.ν hνpos hνq tr' htr'_buc x.1 hx0).2.2.1.2
    have hK0 : 0 ≤ polyPS (C_p (ℓ, i - ℓ)) (N_p (ℓ, i - ℓ)) p.ν (trainPeriod 2 p.ν) x.1 := by
      unfold polyPS
      have hCp0 : 0 < C_p (ℓ, i - ℓ) := hC_p (ℓ, i - ℓ)
      have : 0 ≤ trainPeriod 2 p.ν := by rw [velTail_trainPeriod_two hνpos]; positivity
      positivity
    have hpt := pt_of_wSupNorm_zero (ageJet ℓ (i - ℓ) tr'.v x.1) hK0 hsup x.2
    rw [htr'_v] at hpt
    have hproj := UnforcedLeray.Short.PartIIa.fvs_ageJet_proj_le hG idx
      (fun r z => p.train.v r z idx) (fun _ _ _ => rfl) (i - ℓ) ℓ hx0 x.2
    have hpoly := polyPS_le_gamma_pow (hC_p (ℓ, i - ℓ)).le (N_p (ℓ, i - ℓ)) hνpos hΓ1 hνi hx0 hxΓ
    have hCq : C_p (ℓ, i - ℓ) * (6 : ℝ) ^ (N_p (ℓ, i - ℓ)) ≤ C_max := by
      have hsum : C_p (ℓ, i - ℓ) * (6 : ℝ) ^ (N_p (ℓ, i - ℓ)) ≤
          ∑ q' ∈ S, C_p q' * (6 : ℝ) ^ (N_p q') :=
        Finset.single_le_sum (f := fun q' => C_p q' * (6 : ℝ) ^ (N_p q'))
          (fun q' _ => mul_nonneg (hC_p q').le (pow_nonneg (by norm_num) _)) hqS
      linarith [hC_max_def]
    have hNq : 3 * N_p (ℓ, i - ℓ) ≤ 3 * N_max := by
      have : N_p (ℓ, i - ℓ) ≤ N_max := by rw [hN_max_def]; exact Finset.le_sup hqS
      exact Nat.mul_le_mul_left 3 this
    have hΓpow : Γ ^ (3 * N_p (ℓ, i - ℓ)) ≤ Γ ^ (3 * N_max) := pow_le_pow_right₀ hΓ1 hNq
    calc ‖ageJet ℓ (i - ℓ) (fun r z => p.train.v r z idx) x.1 x.2‖
        ≤ ‖ageJet ℓ (i - ℓ) p.train.v x.1 x.2‖ := hproj
      _ ≤ polyPS (C_p (ℓ, i - ℓ)) (N_p (ℓ, i - ℓ)) p.ν (trainPeriod 2 p.ν) x.1 := hpt
      _ ≤ (C_p (ℓ, i - ℓ) * (6 : ℝ) ^ (N_p (ℓ, i - ℓ))) * Γ ^ (3 * N_p (ℓ, i - ℓ)) := hpoly
      _ ≤ C_max * Γ ^ (3 * N_max) :=
          mul_le_mul hCq hΓpow (by positivity) hC_max.le
  have hsum : ∑ ℓ ∈ Finset.range (i + 1),
      ‖ageJet ℓ (i - ℓ) (fun r z => p.train.v r z idx) x.1 x.2‖ ≤
      10 * (C_max * Γ ^ (3 * N_max)) := by
    calc ∑ ℓ ∈ Finset.range (i + 1),
          ‖ageJet ℓ (i - ℓ) (fun r z => p.train.v r z idx) x.1 x.2‖
        ≤ ∑ _ℓ ∈ Finset.range (i + 1), C_max * Γ ^ (3 * N_max) :=
          Finset.sum_le_sum hage
      _ = ((i : ℝ) + 1) * (C_max * Γ ^ (3 * N_max)) := by
          simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ 10 * (C_max * Γ ^ (3 * N_max)) := by
          have hi10 : (i : ℝ) + 1 ≤ 10 := by exact_mod_cast (show i + 1 ≤ 10 by omega)
          exact mul_le_mul_of_nonneg_right hi10 (by positivity)
  have h3i : (3 : ℝ) ^ i ≤ (3 : ℝ) ^ 9 := pow_le_pow_right₀ (by norm_num) hi
  calc ‖iteratedFDeriv ℝ i (fun y : Coord => p.train.v y.1 y.2 idx) x‖
      ≤ ∑ r : Fin i → Fin 3, |iteratedFDeriv ℝ i (fun y : Coord => p.train.v y.1 y.2 idx) x
          (fun k => UnforcedLeray.Short.PartI.AgeDeriv.LL (r k))| :=
        UnforcedLeray.Short.PartI.AgeDeriv.norm_iteratedFDeriv_le_sum3 _ i x
    _ ≤ ∑ _r : Fin i → Fin 3, ∑ ℓ ∈ Finset.range (i + 1),
          ‖ageJet ℓ (i - ℓ) (fun r z => p.train.v r z idx) x.1 x.2‖ :=
        Finset.sum_le_sum (fun r _ =>
          UnforcedLeray.Short.PartI.jointFromAgeJets_word i (fun r z => p.train.v r z idx) hF x hx0 r)
    _ = (3 : ℝ) ^ i * ∑ ℓ ∈ Finset.range (i + 1),
          ‖ageJet ℓ (i - ℓ) (fun r z => p.train.v r z idx) x.1 x.2‖ := by
        simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ (3 : ℝ) ^ 9 * (10 * (C_max * Γ ^ (3 * N_max))) :=
        mul_le_mul h3i hsum (Finset.sum_nonneg fun _ _ => norm_nonneg _) (by positivity)
    _ = (10 * (3 : ℝ) ^ 9 * C_max) * Γ ^ (3 * N_max) := by ring

/-! ## 2. Cutoff multiplication and operator lifting on `obsBox` -/

private theorem isClosed_obsBox (σ H₁ L₁ : ℝ) : IsClosed (obsBox σ H₁ L₁) :=
  isClosed_Icc.prod (isClosed_univ.prod isClosed_Icc)

private theorem norm_iteratedFDeriv_mul_le_uo {f F : Coord → ℝ}
    (hf : ContDiffOn ℝ ∞ f (Ioi 0 ×ˢ univ)) (hF : ContDiffOn ℝ ∞ F (Ioi 0 ×ˢ univ))
    {y : Coord} (hy : y ∈ (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)))) (i : ℕ) {a B : ℝ}
    (ha : ∀ k ≤ i, ‖iteratedFDeriv ℝ k f y‖ ≤ a) (hB : ∀ k ≤ i, ‖iteratedFDeriv ℝ k F y‖ ≤ B)
    (ha0 : 0 ≤ a) (_hB0 : 0 ≤ B) :
    ‖iteratedFDeriv ℝ i (fun z => f z * F z) y‖ ≤ (((i : ℝ) + 1) * 2 ^ i) * a * B := by
  have hn : (i : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
  have hu : UniqueDiffOn ℝ (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := isOpen_Uo.uniqueDiffOn
  have hw : ∀ (k : ℕ) (g : Coord → ℝ),
      iteratedFDerivWithin ℝ k g (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) y =
        iteratedFDeriv ℝ k g y :=
    fun k g => iteratedFDerivWithin_of_isOpen k isOpen_Uo hy
  have hL := norm_iteratedFDerivWithin_mul_le hf hF hu hy hn
  simp only [hw] at hL
  refine hL.trans ?_
  have hsum : ∑ k ∈ Finset.range (i + 1),
      (i.choose k : ℝ) * ‖iteratedFDeriv ℝ k f y‖ * ‖iteratedFDeriv ℝ (i - k) F y‖ ≤
      ∑ _k ∈ Finset.range (i + 1), (2 : ℝ) ^ i * a * B := by
    apply Finset.sum_le_sum
    intro k hk
    have hk' : k ≤ i := by rw [Finset.mem_range] at hk; omega
    have hch : (i.choose k : ℝ) ≤ 2 ^ i := by exact_mod_cast Nat.choose_le_two_pow i k
    have hA : (i.choose k : ℝ) * ‖iteratedFDeriv ℝ k f y‖ ≤ 2 ^ i * a :=
      mul_le_mul hch (ha k hk') (norm_nonneg _) (by positivity)
    exact mul_le_mul hA (hB (i - k) (by omega)) (norm_nonneg _) (by positivity)
  refine hsum.trans (le_of_eq ?_)
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  push_cast
  ring

/-- Given a scalar profile `g : Coord → ℝ` that is `C^∞` on `s > 0` and has `k`-jets bounded by `B`
for `k ≤ 8` on `obsBox σ H₁ L₁`, the cutoff-multiplied profile `x ↦ ϑ.ϑ x * (x.1 * g x)` is globally
`C^∞`, supported in `obsBox σ H₁ L₁`, and has `k`-jets bounded by `(9 * 256) * (9 * 256 * 2) * Γ² * B`
for `k ≤ 8` everywhere on `Coord`. -/
private theorem obsCut_mul_age_profile {σ H₁ L₁ Γ B : ℝ} (hσ : 0 < σ) (hΓ1 : 1 ≤ Γ)
    (hH₁ : H₁ ≤ Γ) (hB0 : 0 ≤ B) (ϑ : ObsCut σ H₁ L₁ Γ) {g : Coord → ℝ}
    (hg : ContDiffOn ℝ ∞ g (Ioi 0 ×ˢ univ))
    (hg_bd : ∀ k ≤ 8, ∀ x ∈ obsBox σ H₁ L₁, ‖iteratedFDeriv ℝ k g x‖ ≤ B) :
    let φ : Coord → ℝ := fun x => ϑ.ϑ x * (x.1 * g x)
    ContDiff ℝ ∞ φ ∧
      (∀ x, x ∉ obsBox σ H₁ L₁ → φ x = 0) ∧
      (∀ k ≤ 8, ∀ x, ‖iteratedFDeriv ℝ k φ x‖ ≤ 10616832 * Γ ^ 2 * B) := by
  intro φ
  have hΓ0 : 0 ≤ Γ := zero_le_one.trans hΓ1
  have hsupp : ∀ x, x ∉ obsBox σ H₁ L₁ → φ x = 0 := by
    intro x hx
    simp [φ, ϑ.supp x hx]
  have hUo_smooth : ContDiffOn ℝ ∞ φ (Ioi 0 ×ˢ univ) :=
    ϑ.smooth.contDiffOn.mul (contDiff_fst.contDiffOn.mul hg)
  have hcompl_open : IsOpen (obsBox σ H₁ L₁)ᶜ := (isClosed_obsBox σ H₁ L₁).isOpen_compl
  have hsmooth : ContDiff ℝ ∞ φ := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ obsBox σ H₁ L₁
    · have hx0 : 0 < x.1 := lt_of_lt_of_le hσ hx.1.1
      exact hUo_smooth.contDiffAt (isOpen_Uo.mem_nhds ⟨hx0, trivial⟩)
    · have hev : φ =ᶠ[𝓝 x] fun _ => (0 : ℝ) :=
        Filter.eventually_of_mem (hcompl_open.mem_nhds hx) fun y hy => hsupp y hy
      exact contDiffAt_const.congr_of_eventuallyEq hev
  refine ⟨hsmooth, hsupp, ?_⟩
  intro k hk x
  by_cases hx : x ∈ obsBox σ H₁ L₁
  · have hx0 : 0 < x.1 := lt_of_lt_of_le hσ hx.1.1
    have hxU : x ∈ (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := ⟨hx0, trivial⟩
    have hxH : x.1 ≤ Γ := hx.1.2.trans hH₁
    have hx_abs : 1 + |x.1| ≤ 2 * Γ := by
      rw [abs_of_pos hx0]
      linarith
    have hc1 : ∀ m, ‖iteratedFDeriv ℝ m (fun z : Coord => z.1) x‖ ≤ 2 * Γ := by
      intro m
      have h := norm_iteratedFDeriv_clm_le t1Proj norm_t1Proj_le m x
      have h' : ‖iteratedFDeriv ℝ m (fun z : Coord => z.1) x‖ ≤ 1 + |x.1| := by
        simpa [t1Proj, Real.norm_eq_abs] using h
      exact h'.trans hx_abs
    have hsg_bd : ∀ j ≤ 8, ‖iteratedFDeriv ℝ j (fun z : Coord => z.1 * g z) x‖ ≤ 4608 * Γ * B := by
      intro j hj
      have h1 := norm_iteratedFDeriv_mul_le_uo contDiff_fst.contDiffOn hg hxU j
        (fun m _ => hc1 m) (fun m hm => hg_bd m (hm.trans hj) x hx) (by positivity) hB0
      have hj9 : ((j : ℝ) + 1) * 2 ^ j ≤ 9 * 256 := by
        have hj' : (j : ℝ) + 1 ≤ 9 := by exact_mod_cast (show j + 1 ≤ 9 by omega)
        have h2j : (2 : ℝ) ^ j ≤ 2 ^ 8 := pow_le_pow_right₀ (by norm_num) hj
        calc ((j : ℝ) + 1) * 2 ^ j ≤ 9 * 2 ^ 8 :=
              mul_le_mul hj' h2j (by positivity) (by positivity)
          _ = 9 * 256 := by norm_num
      calc ‖iteratedFDeriv ℝ j (fun z : Coord => z.1 * g z) x‖
          ≤ (((j : ℝ) + 1) * 2 ^ j) * (2 * Γ) * B := h1
        _ ≤ (9 * 256) * (2 * Γ) * B :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hj9 (by positivity)) hB0
        _ = 4608 * Γ * B := by ring
    have h2 := norm_iteratedFDeriv_mul_le_uo ϑ.smooth.contDiffOn
      (contDiff_fst.contDiffOn.mul hg) hxU k
      (fun m hm => ϑ.bounded m (hm.trans hk) x)
      (fun m hm => hsg_bd m (hm.trans hk)) hΓ0 (by positivity)
    have hk9 : ((k : ℝ) + 1) * 2 ^ k ≤ 2304 := by
      have hk' : (k : ℝ) + 1 ≤ 9 := by exact_mod_cast (show k + 1 ≤ 9 by omega)
      have h2k : (2 : ℝ) ^ k ≤ 2 ^ 8 := pow_le_pow_right₀ (by norm_num) hk
      calc ((k : ℝ) + 1) * 2 ^ k ≤ 9 * 2 ^ 8 :=
            mul_le_mul hk' h2k (by positivity) (by positivity)
        _ = 2304 := by norm_num
    calc ‖iteratedFDeriv ℝ k φ x‖
        ≤ (((k : ℝ) + 1) * 2 ^ k) * Γ * (4608 * Γ * B) := h2
      _ ≤ 2304 * Γ * (4608 * Γ * B) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hk9 hΓ0) (by positivity)
      _ = 10616832 * Γ ^ 2 * B := by ring
  · have hev : φ =ᶠ[𝓝 x] fun _ => (0 : ℝ) :=
      Filter.eventually_of_mem (hcompl_open.mem_nhds hx) fun y hy => hsupp y hy
    rw [RingJ.vanish_norm φ x hev k]
    positivity

/-- The spatial slice directional derivative agrees with the joint directional derivative on `s > 0`. -/
private theorem slice_fderiv_eq_joint (v : ℝ → UnforcedLeray.Cyl.Plane → ℝ)
    (hv : ContDiffOn ℝ ∞ (fun x : Coord => v x.1 x.2) (Ioi 0 ×ˢ univ))
    {x : Coord} (hx : x ∈ (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)))) (e : UnforcedLeray.Cyl.Plane) :
    fderiv ℝ (fun z => v x.1 z) x.2 e =
      fderiv ℝ (fun y : Coord => v y.1 y.2) x (0, e) := by
  rcases x with ⟨s, z⟩
  have hdiff : DifferentiableAt ℝ (fun y : Coord => v y.1 y.2) (s, z) :=
    (hv.differentiableOn (by simp)).differentiableAt (isOpen_Uo.mem_nhds hx)
  have hG : HasFDerivAt (fun w : UnforcedLeray.Cyl.Plane => v s w)
      ((fderiv ℝ (fun y : Coord => v y.1 y.2) (s, z)).comp
        ((0 : UnforcedLeray.Cyl.Plane →L[ℝ] ℝ).prod
          (ContinuousLinearMap.id ℝ UnforcedLeray.Cyl.Plane))) z :=
    hdiff.hasFDerivAt.comp z ((hasFDerivAt_const s z).prodMk (hasFDerivAt_id z))
  rw [hG.fderiv]
  simp

/-- Elementary matrix unit `(i, j)` on `CMerid = EuclideanSpace ℂ (Fin 2)`: sends `w` to
`w j • single i 1`. -/
private def basisOp (i j : Fin 2) : CMerid →L[ℂ] CMerid :=
  (ContinuousLinearMap.toSpanSingleton ℂ (EuclideanSpace.single i (1 : ℂ))).comp
    (EuclideanSpace.proj j : CMerid →L[ℂ] ℂ)

private theorem basisOp_apply (i j : Fin 2) (w : CMerid) (k : Fin 2) :
    basisOp i j w k = w j * (if k = i then (1 : ℂ) else 0) := by
  simp [basisOp]

private theorem norm_basisOp_le (i j : Fin 2) : ‖basisOp i j‖ ≤ 1 := by
  unfold basisOp
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  rw [ContinuousLinearMap.norm_toSpanSingleton, PiLp.norm_single, norm_one, one_mul]
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun w => ?_)
  simpa using PiLp.norm_apply_le w j

/-! ## 3. Main theorem: `flatKObsOpPackage_of` -/

/-- **Leaf 1 (`PartII-b:T20/1`, `FlatKObsOpPackage`, SP 2007–2023)**:
For any smooth cutoff `ϑ : ObsCut σ H₁ L₁ Γ` on `obsBox σ H₁ L₁` (`σ > 0`), the flat linearized
interaction `(b, gq, gη) ↦ ϑ • flatK p.train b gq gη` is realized by a smooth observation operator
`ObsOp σ H₁ L₁ (C_B * Γ ^ k_B)`. -/
theorem flatKObsOpPackage_of : UnforcedLeray.Short.IIb.FlatKObsOpPackage := by
  obtain ⟨N_v, C_v, ν₀, hC_v, hν₀, hVel⟩ := train_vel_coord_jet_bound
  set C_B : ℝ := 4 * 10616832 * C_v
  have hC_B : 0 < C_B := by dsimp [C_B]; positivity
  refine ⟨N_v + 2, C_B, ν₀, hC_B, hν₀, ?_⟩
  intro p d dm dp hBG hνle Γ σ H₁ L₁ hΓ1 _hνΓ hνi _hσi hH₁ _hL₁ hσ ϑ
  have hΓ0 : 0 ≤ Γ := zero_le_one.trans hΓ1
  set B : ℝ := C_v * Γ ^ N_v
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  have hG : ContDiffOn ℝ ∞ (fun y : Coord => p.train.v y.1 y.2) (Ioi 0 ×ˢ univ) :=
    p.train.isTrain.smooth_v.mono (Set.prod_mono Set.Ioi_subset_Ici_self Subset.rfl)
  have hv_sm : ∀ idx : Fin 2,
      ContDiffOn ℝ ∞ (fun y : Coord => p.train.v y.1 y.2 idx) (Ioi 0 ×ˢ univ) := fun idx =>
    (EuclideanSpace.proj idx : UnforcedLeray.Train.Vec →L[ℝ] ℝ).contDiff.comp_contDiffOn hG
  have hv_bd : ∀ (idx : Fin 2) (k : ℕ), k ≤ 9 → ∀ x ∈ obsBox σ H₁ L₁,
      ‖iteratedFDeriv ℝ k (fun y : Coord => p.train.v y.1 y.2 idx) x‖ ≤ B := by
    intro idx k hk x hx
    exact hVel p d dm dp hBG hνle Γ hΓ1 hνi idx k hk x
      (lt_of_lt_of_le hσ hx.1.1) (hx.1.2.trans hH₁)
  -- Spatial derivative profiles `dv idx e x = fderiv (z ↦ p.train.v x.1 z idx) x.2 e`
  have hdv_sm : ∀ (idx : Fin 2) (e : UnforcedLeray.Cyl.Plane),
      ContDiffOn ℝ ∞ (fun x : Coord => fderiv ℝ (fun z => p.train.v x.1 z idx) x.2 e)
        (Ioi 0 ×ˢ univ) := by
    intro idx e
    refine (contDiffOn_fderiv_apply (hv_sm idx) (0, e)).congr ?_
    intro x hx
    exact slice_fderiv_eq_joint (fun r z => p.train.v r z idx) (hv_sm idx) hx e
  have hdv_bd : ∀ (idx : Fin 2) (e : UnforcedLeray.Cyl.Plane), ‖e‖ ≤ 1 →
      ∀ k ≤ 8, ∀ x ∈ obsBox σ H₁ L₁,
        ‖iteratedFDeriv ℝ k (fun y : Coord => fderiv ℝ (fun z => p.train.v y.1 z idx) y.2 e) x‖ ≤
          B := by
    intro idx e he k hk x hx
    have hxU : x ∈ (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) :=
      ⟨lt_of_lt_of_le hσ hx.1.1, trivial⟩
    have hev : (fun y : Coord => fderiv ℝ (fun z => p.train.v y.1 z idx) y.2 e) =ᶠ[𝓝 x]
        (fun y : Coord => fderiv ℝ (fun w : Coord => p.train.v w.1 w.2 idx) y (0, e)) :=
      Filter.eventually_of_mem (isOpen_Uo.mem_nhds hxU) fun y hy =>
        slice_fderiv_eq_joint (fun r z => p.train.v r z idx) (hv_sm idx) hy e
    rw [(hev.iteratedFDeriv ℝ k).eq_of_nhds]
    have h0e : ‖((0 : ℝ), e)‖ ≤ 1 := by
      rw [Prod.norm_def]
      exact max_le (by simp) he
    refine (norm_iteratedFDeriv_fderiv_apply_le (hv_sm idx) hxU (0, e) k).trans ?_
    calc ‖((0 : ℝ), e)‖ * ‖iteratedFDeriv ℝ (k + 1) (fun w : Coord => p.train.v w.1 w.2 idx) x‖
        ≤ 1 * B := mul_le_mul h0e (hv_bd idx (k + 1) (by omega) x hx) (norm_nonneg _) zero_le_one
      _ = B := one_mul B
  have he10 : ‖((1 : ℝ), (0 : ℝ))‖ ≤ 1 := by simp [Prod.norm_def]
  have he01 : ‖((0 : ℝ), (1 : ℝ))‖ ≤ 1 := by simp [Prod.norm_def]
  -- Six scalar cutoff-multiplied coefficients
  set φ_q : Coord → ℝ := fun x => ϑ.ϑ x * (x.1 * p.train.v x.1 x.2 0)
  set φ_η : Coord → ℝ := fun x => ϑ.ϑ x * (x.1 * p.train.v x.1 x.2 1)
  set φ_00 : Coord → ℝ := fun x => ϑ.ϑ x * (x.1 * fderiv ℝ (fun z => p.train.v x.1 z 0) x.2 (1, 0))
  set φ_01 : Coord → ℝ := fun x => ϑ.ϑ x * (x.1 * fderiv ℝ (fun z => p.train.v x.1 z 0) x.2 (0, 1))
  set φ_10 : Coord → ℝ := fun x => ϑ.ϑ x * (x.1 * fderiv ℝ (fun z => p.train.v x.1 z 1) x.2 (1, 0))
  set φ_11 : Coord → ℝ := fun x => ϑ.ϑ x * (x.1 * fderiv ℝ (fun z => p.train.v x.1 z 1) x.2 (0, 1))
  obtain ⟨hφq_sm, hφq_supp, hφq_bd⟩ := obsCut_mul_age_profile hσ hΓ1 hH₁ hB0 ϑ (hv_sm 0)
    (fun k hk => hv_bd 0 k (by omega))
  obtain ⟨hφη_sm, hφη_supp, hφη_bd⟩ := obsCut_mul_age_profile hσ hΓ1 hH₁ hB0 ϑ (hv_sm 1)
    (fun k hk => hv_bd 1 k (by omega))
  obtain ⟨hφ00_sm, hφ00_supp, hφ00_bd⟩ := obsCut_mul_age_profile hσ hΓ1 hH₁ hB0 ϑ
    (hdv_sm 0 (1, 0)) (hdv_bd 0 (1, 0) he10)
  obtain ⟨hφ01_sm, hφ01_supp, hφ01_bd⟩ := obsCut_mul_age_profile hσ hΓ1 hH₁ hB0 ϑ
    (hdv_sm 0 (0, 1)) (hdv_bd 0 (0, 1) he01)
  obtain ⟨hφ10_sm, hφ10_supp, hφ10_bd⟩ := obsCut_mul_age_profile hσ hΓ1 hH₁ hB0 ϑ
    (hdv_sm 1 (1, 0)) (hdv_bd 1 (1, 0) he10)
  obtain ⟨hφ11_sm, hφ11_supp, hφ11_bd⟩ := obsCut_mul_age_profile hσ hΓ1 hH₁ hB0 ϑ
    (hdv_sm 1 (0, 1)) (hdv_bd 1 (0, 1) he01)
  -- Lift scalar coefficients to operator-valued fields `Coord → (CMerid →L[ℂ] CMerid)`
  set idOp : CMerid →L[ℂ] CMerid := ContinuousLinearMap.id ℂ CMerid
  set Aq : Coord → (CMerid →L[ℂ] CMerid) := fun x => φ_q x • idOp
  set Aeta : Coord → (CMerid →L[ℂ] CMerid) := fun x => φ_η x • idOp
  set A0 : Coord → (CMerid →L[ℂ] CMerid) := fun x =>
    (φ_00 x • basisOp 0 0 + φ_01 x • basisOp 0 1) +
      (φ_10 x • basisOp 1 0 + φ_11 x • basisOp 1 1)
  have hsmul_cd : ∀ {f : Coord → ℝ}, ContDiff ℝ ∞ f →
      ∀ M : CMerid →L[ℂ] CMerid, ContDiff ℝ ∞ (fun x => f x • M) := by
    intro f hf M
    exact (ContinuousLinearMap.toSpanSingleton ℝ M).contDiff.comp hf
  have hAq_sm : ContDiff ℝ ∞ Aq := hsmul_cd hφq_sm idOp
  have hAeta_sm : ContDiff ℝ ∞ Aeta := hsmul_cd hφη_sm idOp
  have hA0_sm : ContDiff ℝ ∞ A0 :=
    ((hsmul_cd hφ00_sm _).add (hsmul_cd hφ01_sm _)).add
      ((hsmul_cd hφ10_sm _).add (hsmul_cd hφ11_sm _))
  have hsmul_bd : ∀ {f : Coord → ℝ} (hf : ContDiff ℝ ∞ f)
      (hbd : ∀ k ≤ 8, ∀ x, ‖iteratedFDeriv ℝ k f x‖ ≤ 10616832 * Γ ^ 2 * B)
      (M : CMerid →L[ℂ] CMerid) (hM : ‖M‖ ≤ 1) (k : ℕ), k ≤ 8 → ∀ x : Coord,
        ‖iteratedFDeriv ℝ k (fun y => f y • M) x‖ ≤ 10616832 * Γ ^ 2 * B := by
    intro f hf hbd M hM k hk x
    refine (RingJ.smulVec_norm f hf M k x).trans ?_
    calc ‖M‖ * ‖iteratedFDeriv ℝ k f x‖
        ≤ 1 * (10616832 * Γ ^ 2 * B) :=
          mul_le_mul hM (hbd k hk x) (norm_nonneg _) zero_le_one
      _ = 10616832 * Γ ^ 2 * B := one_mul _
  have hid_le : ‖idOp‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  have h1_le_4 : 10616832 * Γ ^ 2 * B ≤ C_B * Γ ^ (N_v + 2) := by
    have heq : 4 * (10616832 * Γ ^ 2 * B) = C_B * Γ ^ (N_v + 2) := by
      dsimp [C_B, B]
      rw [pow_add]
      ring
    linarith [show 0 ≤ 10616832 * Γ ^ 2 * B by positivity]
  refine ⟨⟨Aq, Aeta, A0, ⟨hAq_sm, hAeta_sm, hA0_sm⟩, ?_, ?_⟩, ?_⟩
  · intro x hx
    have hq0 : φ_q x = 0 := hφq_supp x hx
    have hη0 : φ_η x = 0 := hφη_supp x hx
    have h00 : φ_00 x = 0 := hφ00_supp x hx
    have h01 : φ_01 x = 0 := hφ01_supp x hx
    have h10 : φ_10 x = 0 := hφ10_supp x hx
    have h11 : φ_11 x = 0 := hφ11_supp x hx
    refine ⟨?_, ?_, ?_⟩
    · dsimp only [Aq]; rw [hq0]; exact zero_smul ℝ idOp
    · dsimp only [Aeta]; rw [hη0]; exact zero_smul ℝ idOp
    · ext w k
      simp [A0, h00, h01, h10, h11]
  · intro k hk x
    refine ⟨(hsmul_bd hφq_sm hφq_bd idOp hid_le k hk x).trans h1_le_4,
      (hsmul_bd hφη_sm hφη_bd idOp hid_le k hk x).trans h1_le_4, ?_⟩
    have hL := RingJ.addV_norm (fun y => φ_00 y • basisOp 0 0) (fun y => φ_01 y • basisOp 0 1)
      (hsmul_cd hφ00_sm _) (hsmul_cd hφ01_sm _) k x
    have hR := RingJ.addV_norm (fun y => φ_10 y • basisOp 1 0) (fun y => φ_11 y • basisOp 1 1)
      (hsmul_cd hφ10_sm _) (hsmul_cd hφ11_sm _) k x
    have hLR := RingJ.addV_norm
      (fun y => φ_00 y • basisOp 0 0 + φ_01 y • basisOp 0 1)
      (fun y => φ_10 y • basisOp 1 0 + φ_11 y • basisOp 1 1)
      ((hsmul_cd hφ00_sm _).add (hsmul_cd hφ01_sm _))
      ((hsmul_cd hφ10_sm _).add (hsmul_cd hφ11_sm _)) k x
    have b00 := hsmul_bd hφ00_sm hφ00_bd (basisOp 0 0) (norm_basisOp_le 0 0) k hk x
    have b01 := hsmul_bd hφ01_sm hφ01_bd (basisOp 0 1) (norm_basisOp_le 0 1) k hk x
    have b10 := hsmul_bd hφ10_sm hφ10_bd (basisOp 1 0) (norm_basisOp_le 1 0) k hk x
    have b11 := hsmul_bd hφ11_sm hφ11_bd (basisOp 1 1) (norm_basisOp_le 1 1) k hk x
    have heq : 4 * (10616832 * Γ ^ 2 * B) = C_B * Γ ^ (N_v + 2) := by
      dsimp [C_B, B]
      rw [pow_add]
      ring
    linarith
  · intro b gq gη x
    ext i
    simp only [ObsOp.apply, Aq, Aeta, A0, idOp, add_apply, smul_apply,
      ContinuousLinearMap.id_apply, PiLp.add_apply, PiLp.smul_apply, basisOp_apply,
      Complex.real_smul, smul_eq_mul, flatK, φ_q, φ_η, φ_00, φ_01, φ_10, φ_11]
    fin_cases i <;>
      · simp
        ring

end UnforcedLeray.Short.IIb
