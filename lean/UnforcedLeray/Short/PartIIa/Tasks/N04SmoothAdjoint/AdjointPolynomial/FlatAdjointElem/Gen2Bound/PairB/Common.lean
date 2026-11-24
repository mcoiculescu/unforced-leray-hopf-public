import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N04_2_2_3
import UnforcedLeray.Short.PartIIa.Tasks.N04SmoothAdjoint.AdjointPolynomial.FlatAdjointElem.Gen1Bound

/-!
# Shared tools for the second-order adjoint bounds (`Gen2Bound`, pairs A and B)

Source of record: `the November 2 reference manuscript`,
lines 1809-1835. Mirrors `Gen1Bound` one derivative order higher.

1. `Bsum h`: the pointwise sum of all weighted derivatives `|η|^j ‖D^m S^a h‖` (`a < 2`, `j < 3`,
   `m < 5`) entering `flatProjMomentNorm c h`; its `L²(measureH c)` norm is at most
   `flatProjMomentNorm c h`, so every profile dominated pointwise by `K * Bsum h` lies in `L²`
   with norm at most `K * flatProjMomentNorm c h`.
2. `IsDer`: profiles obtained from `S^a h` by `m` constant-coefficient derivatives (with a
   constant `K`), closed under `∂_q`, `∂_η`, `∂_s`, sums and the planar Laplacian.
3. `Inner`: smooth, periodic, band-supported profiles dominated by `K * Bsum h`; their causal
   integrals obey the resolvent bound `γ_*⁻¹ K flatProjMomentNorm c h`.
4. Commutation of `∂_q`, `∂_η`, `Δ` with the multiplier `ν s`, and `IsDiffProfile` for `ν s w`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff InnerProductSpace

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0224 UnforcedLeray.B0226
open FlatAdjointElemAux

namespace Gen2Aux

/-! ### 1. The total weighted derivative `Bsum` -/

/-- One weighted derivative `|η|^j ‖D^m S^a h‖`. -/
def bterm (h : Profile → MeridC) (a j m : ℕ) (p : Profile) : ℝ :=
  |p.2.2| ^ j * ‖iteratedFDeriv ℝ m (opS^[a] h) p‖

/-- Sum of all weighted derivatives entering `flatProjMomentNorm`. -/
def Bsum (h : Profile → MeridC) (p : Profile) : ℝ :=
  ∑ a ∈ Finset.range 2, ∑ j ∈ Finset.range 3, ∑ m ∈ Finset.range 5, bterm h a j m p

theorem bterm_nonneg (h : Profile → MeridC) (a j m : ℕ) (p : Profile) : 0 ≤ bterm h a j m p := by
  unfold bterm
  positivity

theorem Bsum_nonneg (h : Profile → MeridC) (p : Profile) : 0 ≤ Bsum h p := by
  unfold Bsum
  exact Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun j _ =>
    Finset.sum_nonneg fun m _ => bterm_nonneg h a j m p

theorem bterm_le_Bsum (h : Profile → MeridC) {a j m : ℕ} (ha : a < 2) (hj : j < 3) (hm : m < 5)
    (p : Profile) : bterm h a j m p ≤ Bsum h p := by
  unfold Bsum
  have h1 : bterm h a j m p ≤ ∑ m' ∈ Finset.range 5, bterm h a j m' p :=
    Finset.single_le_sum (f := fun m' => bterm h a j m' p)
      (fun m' _ => bterm_nonneg h a j m' p) (Finset.mem_range.2 hm)
  have h2 : ∑ m' ∈ Finset.range 5, bterm h a j m' p ≤
      ∑ j' ∈ Finset.range 3, ∑ m' ∈ Finset.range 5, bterm h a j' m' p :=
    Finset.single_le_sum (f := fun j' => ∑ m' ∈ Finset.range 5, bterm h a j' m' p)
      (fun j' _ => Finset.sum_nonneg fun m' _ => bterm_nonneg h a j' m' p)
      (Finset.mem_range.2 hj)
  have h3 : ∑ j' ∈ Finset.range 3, ∑ m' ∈ Finset.range 5, bterm h a j' m' p ≤
      ∑ a' ∈ Finset.range 2, ∑ j' ∈ Finset.range 3, ∑ m' ∈ Finset.range 5, bterm h a' j' m' p :=
    Finset.single_le_sum
      (f := fun a' => ∑ j' ∈ Finset.range 3, ∑ m' ∈ Finset.range 5, bterm h a' j' m' p)
      (fun a' _ => Finset.sum_nonneg fun j' _ => Finset.sum_nonneg fun m' _ =>
        bterm_nonneg h a' j' m' p)
      (Finset.mem_range.2 ha)
  exact h1.trans (h2.trans h3)

theorem continuous_bterm {h : Profile → MeridC} (hs : ContDiff ℝ ∞ h) (a j m : ℕ) :
    Continuous (bterm h a j m) := by
  unfold bterm
  have hD : Continuous fun p => iteratedFDeriv ℝ m (opS^[a] h) p :=
    (contDiff_opS_iter a hs).continuous_iteratedFDeriv (by exact_mod_cast le_top)
  have hE : Continuous fun p : Profile => p.2.2 := continuous_snd.comp continuous_snd
  exact (hE.abs.pow j).mul hD.norm

theorem continuous_Bsum {h : Profile → MeridC} (hs : ContDiff ℝ ∞ h) :
    Continuous (Bsum h) := by
  unfold Bsum
  exact continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun j _ =>
    continuous_finsetSum _ fun m _ => continuous_bterm hs a j m

theorem finset_sum_bdd {ι : Type*} (s : Finset ι) (f : ι → Profile → ℝ)
    (hf : ∀ i ∈ s, ∃ M : ℝ, ∀ p, f i p ≤ M) : ∃ M : ℝ, ∀ p, ∑ i ∈ s, f i p ≤ M := by
  choose! M hM using hf
  exact ⟨∑ i ∈ s, M i, fun p => Finset.sum_le_sum fun i hi => hM i hi p⟩

theorem Bsum_bdd {c σ H1 : ℝ} {h : Profile → MeridC} (hh : IsFlatLerayRep c σ H1 h) :
    ∃ M : ℝ, ∀ p, Bsum h p ≤ M := by
  unfold Bsum
  refine finset_sum_bdd _ _ fun a ha => finset_sum_bdd _ _ fun j hj =>
    finset_sum_bdd _ _ fun m hm => ?_
  exact hh.bounded_moments a ha j hj m hm

theorem memLp_bterm {c σ H1 : ℝ} {h : Profile → MeridC} (hh : IsFlatLerayRep c σ H1 h)
    {a j m : ℕ} (ha : a ∈ Finset.range 2) (hj : j ∈ Finset.range 3) (hm : m ∈ Finset.range 5) :
    MemLp (bterm h a j m) 2 (measureH c) := by
  have hcont := continuous_bterm hh.smooth a j m
  rw [memLp_two_iff_integrable_sq_norm hcont.aestronglyMeasurable]
  refine (hh.integrable_moments a ha j hj m hm).congr (Eventually.of_forall fun p => ?_)
  simp only [Real.norm_eq_abs, sq_abs, bterm, mul_pow]

theorem eLpNorm_bterm_le {c σ H1 : ℝ} {h : Profile → MeridC} (hh : IsFlatLerayRep c σ H1 h)
    {a j m : ℕ} (ha : a ∈ Finset.range 2) (hj : j ∈ Finset.range 3) (hm : m ∈ Finset.range 5) :
    eLpNorm (bterm h a j m) 2 (measureH c) ≤
      ENNReal.ofReal ((∫ p, (|p.2.2| ^ j) ^ 2 *
        ‖iteratedFDeriv ℝ m (opS^[a] h) p‖ ^ 2 ∂(measureH c)) ^ (1 / 2 : ℝ)) := by
  have hb := memLp_bterm hh ha hj hm
  rw [← ENNReal.ofReal_toReal hb.eLpNorm_ne_top]
  refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
  have hsq := toReal_eLpNorm_two_sq hb.aestronglyMeasurable
  have hint : ∫ x, ‖bterm h a j m x‖ ^ 2 ∂(measureH c) =
      ∫ p, (|p.2.2| ^ j) ^ 2 * ‖iteratedFDeriv ℝ m (opS^[a] h) p‖ ^ 2 ∂(measureH c) := by
    refine integral_congr_ae (Eventually.of_forall fun p => ?_)
    simp only [Real.norm_eq_abs, sq_abs, bterm, mul_pow]
  rw [hint] at hsq
  rw [← hsq, ← Real.sqrt_eq_rpow, Real.sqrt_sq ENNReal.toReal_nonneg]

theorem eLpNorm_fun_sum_le {c : ℝ} {ι : Type*} (s : Finset ι) (f : ι → Profile → ℝ)
    (hf : ∀ i ∈ s, Continuous (f i)) :
    eLpNorm (fun p => ∑ i ∈ s, f i p) 2 (measureH c) ≤ ∑ i ∈ s, eLpNorm (f i) 2 (measureH c) := by
  have hfun : (fun p => ∑ i ∈ s, f i p) = ∑ i ∈ s, f i := by
    funext p
    simp [Finset.sum_apply]
  rw [hfun]
  exact eLpNorm_sum_le (fun i hi => (hf i hi).aestronglyMeasurable) one_le_two

theorem eLpNorm_Bsum_le {c σ H1 : ℝ} {h : Profile → MeridC} (hh : IsFlatLerayRep c σ H1 h) :
    eLpNorm (Bsum h) 2 (measureH c) ≤ ENNReal.ofReal (flatProjMomentNorm c h) := by
  set I : ℕ → ℕ → ℕ → ℝ := fun a j m => (∫ p, (|p.2.2| ^ j) ^ 2 *
    ‖iteratedFDeriv ℝ m (opS^[a] h) p‖ ^ 2 ∂(measureH c)) ^ (1 / 2 : ℝ) with hI
  have hI0 : ∀ a j m, 0 ≤ I a j m := fun a j m =>
    Real.rpow_nonneg (integral_nonneg fun p => mul_nonneg (sq_nonneg _) (sq_nonneg _)) _
  have hcont := continuous_bterm hh.smooth
  have step1 : eLpNorm (Bsum h) 2 (measureH c) ≤ ∑ a ∈ Finset.range 2,
      eLpNorm (fun p => ∑ j ∈ Finset.range 3, ∑ m ∈ Finset.range 5, bterm h a j m p) 2
        (measureH c) :=
    eLpNorm_fun_sum_le _ _ fun a _ => continuous_finsetSum _ fun j _ =>
      continuous_finsetSum _ fun m _ => hcont a j m
  have step2 : ∀ a ∈ Finset.range 2,
      eLpNorm (fun p => ∑ j ∈ Finset.range 3, ∑ m ∈ Finset.range 5, bterm h a j m p) 2
        (measureH c) ≤ ∑ j ∈ Finset.range 3, ∑ m ∈ Finset.range 5,
          ENNReal.ofReal (I a j m) := by
    intro a ha
    refine (eLpNorm_fun_sum_le _ _ fun j _ =>
      continuous_finsetSum _ fun m _ => hcont a j m).trans ?_
    refine Finset.sum_le_sum fun j hj => ?_
    refine (eLpNorm_fun_sum_le _ _ fun m _ => hcont a j m).trans ?_
    exact Finset.sum_le_sum fun m hm => eLpNorm_bterm_le hh ha hj hm
  have step3 : ∑ a ∈ Finset.range 2, ∑ j ∈ Finset.range 3, ∑ m ∈ Finset.range 5,
      ENNReal.ofReal (I a j m) = ENNReal.ofReal (flatProjMomentNorm c h) := by
    unfold flatProjMomentNorm
    rw [ENNReal.ofReal_sum_of_nonneg fun a _ => Finset.sum_nonneg fun j _ =>
      Finset.sum_nonneg fun m _ => hI0 a j m]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [ENNReal.ofReal_sum_of_nonneg fun j _ => Finset.sum_nonneg fun m _ => hI0 a j m]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ENNReal.ofReal_sum_of_nonneg fun m _ => hI0 a j m]
  rw [← step3]
  exact step1.trans (Finset.sum_le_sum step2)

/-! ### 2. `L²` bounds by domination -/

/-- `f ∈ L²(measureH c)` with norm at most `B`. -/
def L2B (c : ℝ) (f : Profile → MeridC) (B : ℝ) : Prop :=
  ∃ hf : MemLp f 2 (measureH c), ‖hf.toLp f‖ ≤ B

theorem L2B.mono {c : ℝ} {f : Profile → MeridC} {B B' : ℝ} (hf : L2B c f B) (hB : B ≤ B') :
    L2B c f B' := by
  obtain ⟨hm, hb⟩ := hf
  exact ⟨hm, hb.trans hB⟩

theorem L2B.add {c : ℝ} {f g : Profile → MeridC} {B1 B2 : ℝ} (hf : L2B c f B1) (hg : L2B c g B2) :
    L2B c (f + g) (B1 + B2) := by
  obtain ⟨hm1, hb1⟩ := hf
  obtain ⟨hm2, hb2⟩ := hg
  exact ⟨hm1.add hm2, (norm_toLp_add_le hm1 hm2).trans (add_le_add hb1 hb2)⟩

theorem L2B.sub {c : ℝ} {f g : Profile → MeridC} {B1 B2 : ℝ} (hf : L2B c f B1) (hg : L2B c g B2) :
    L2B c (f - g) (B1 + B2) := by
  obtain ⟨hm1, hb1⟩ := hf
  obtain ⟨hm2, hb2⟩ := hg
  exact ⟨hm1.sub hm2, (norm_toLp_sub_le hm1 hm2).trans (add_le_add hb1 hb2)⟩

theorem L2B.smul {c : ℝ} {f : Profile → MeridC} {B : ℝ} (r : ℝ) (hf : L2B c f B) :
    L2B c (r • f) (|r| * B) := by
  obtain ⟨hm, hb⟩ := hf
  refine ⟨hm.const_smul r, ?_⟩
  rw [norm_toLp_const_smul_eq r hm]
  exact mul_le_mul_of_nonneg_left hb (abs_nonneg r)

theorem L2B.congr {c : ℝ} {f g : Profile → MeridC} {B : ℝ} (hf : L2B c f B) (hfg : f = g) :
    L2B c g B := hfg ▸ hf

theorem L2B_of_le_Bsum {c σ H1 : ℝ} {h : Profile → MeridC} (hh : IsFlatLerayRep c σ H1 h)
    {u : Profile → MeridC} (hu : AEStronglyMeasurable u (measureH c)) {K : ℝ} (hK : 0 ≤ K)
    (hpt : ∀ p, ‖u p‖ ≤ K * Bsum h p) :
    L2B c u (K * flatProjMomentNorm c h) := by
  have hle : eLpNorm u 2 (measureH c) ≤ ENNReal.ofReal K * eLpNorm (Bsum h) 2 (measureH c) :=
    eLpNorm_le_mul_eLpNorm_of_ae_le_mul (Eventually.of_forall fun p => by
      rw [Real.norm_of_nonneg (Bsum_nonneg h p)]
      exact hpt p) 2
  have hle2 : eLpNorm u 2 (measureH c) ≤ ENNReal.ofReal (K * flatProjMomentNorm c h) := by
    rw [ENNReal.ofReal_mul hK]
    exact hle.trans (by gcongr; exact eLpNorm_Bsum_le hh)
  have hU : MemLp u 2 (measureH c) := ⟨hu, hle2.trans_lt ENNReal.ofReal_lt_top⟩
  refine ⟨hU, ?_⟩
  rw [Lp.norm_toLp]
  have h3 := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle2
  rwa [ENNReal.toReal_ofReal (mul_nonneg hK (flatProjMomentNorm_nonneg c h))] at h3

/-- The outer multiplier `ν s` on profiles vanishing above `H₁`. -/
theorem L2B.outer {c ν H1 B : ℝ} (hν : 0 < ν) (hH1 : 0 < H1) {F G : Profile → MeridC}
    (hF : L2B c F B) (hsupp : ∀ p : Profile, H1 < p.1 → F p = 0)
    (heq : ∀ p : Profile, 0 < p.1 → G p = (ν * p.1) • F p) :
    L2B c G (ν * H1 * B) := by
  obtain ⟨hm, hb⟩ := hF
  exact ⟨memLp_of_eqOn_pos_nuSMul_one hν hH1 hm hsupp heq,
    (norm_toLp_of_eqOn_pos_nuSMul_one_le hν hH1 hm hsupp heq).trans
      (mul_le_mul_of_nonneg_left hb (mul_pos hν hH1).le)⟩

/-! ### 3. Derivative chains `IsDer` -/

/-- `u` is smooth, `c`-periodic, supported in the age band, and its derivatives of every order
`n` are dominated by `K` times the derivatives of order `n + m` of `S^a h`. -/
structure IsDer (c σ H1 : ℝ) (h : Profile → MeridC) (a m : ℕ) (K : ℝ)
    (u : Profile → MeridC) : Prop where
  smooth : ContDiff ℝ ∞ u
  periodic : QPeriodic c u
  support_s : ∀ p : Profile, p.1 < σ ∨ H1 < p.1 → u p = 0
  bound : ∀ (n : ℕ) (p : Profile),
    ‖iteratedFDeriv ℝ n u p‖ ≤ K * ‖iteratedFDeriv ℝ (n + m) (opS^[a] h) p‖

theorem isDer_base {c σ H1 : ℝ} {h : Profile → MeridC} (hh : IsFlatLerayRep c σ H1 h) (a : ℕ) :
    IsDer c σ H1 h a 0 1 (opS^[a] h) where
  smooth := contDiff_opS_iter a hh.smooth
  periodic := periodic_opS_iter a hh.periodic
  support_s := support_s_opS_iter a hh.support_s
  bound n p := by simp

theorem isDer_h {c σ H1 : ℝ} {h : Profile → MeridC} (hh : IsFlatLerayRep c σ H1 h) :
    IsDer c σ H1 h 0 0 1 h :=
  isDer_base hh 0

theorem isDer_Sh {c σ H1 : ℝ} {h : Profile → MeridC} (hh : IsFlatLerayRep c σ H1 h) :
    IsDer c σ H1 h 1 0 1 (opS h) :=
  isDer_base hh 1

theorem norm_iteratedFDeriv_pdS_le {w : Profile → MeridC} (hw : ContDiff ℝ ∞ w)
    (m : ℕ) (p : Profile) :
    ‖iteratedFDeriv ℝ m (pdS w) p‖ ≤ ‖iteratedFDeriv ℝ (m + 1) w p‖ := by
  refine norm_iteratedFDeriv_fderiv_apply_le hw ?_ m p
  simp [Prod.norm_def]

theorem IsDer.dQ {c σ H1 : ℝ} {h u : Profile → MeridC} {a m : ℕ} {K : ℝ}
    (hu : IsDer c σ H1 h a m K u) : IsDer c σ H1 h a (m + 1) K (pdQ u) where
  smooth := contDiff_pdQ hu.smooth
  periodic := periodic_pdQ hu.periodic
  support_s := support_s_pdQ hu.support_s
  bound n p := by
    have h1 := norm_iteratedFDeriv_pdQ_le hu.smooth n p
    have h2 := hu.bound (n + 1) p
    rw [show n + 1 + m = n + (m + 1) by omega] at h2
    exact h1.trans h2

theorem IsDer.dEta {c σ H1 : ℝ} {h u : Profile → MeridC} {a m : ℕ} {K : ℝ}
    (hu : IsDer c σ H1 h a m K u) : IsDer c σ H1 h a (m + 1) K (pdEta u) where
  smooth := contDiff_pdEta hu.smooth
  periodic := periodic_pdEta hu.periodic
  support_s := support_s_pdEta hu.support_s
  bound n p := by
    have h1 := norm_iteratedFDeriv_pdEta_le hu.smooth n p
    have h2 := hu.bound (n + 1) p
    rw [show n + 1 + m = n + (m + 1) by omega] at h2
    exact h1.trans h2

theorem IsDer.dS {c σ H1 : ℝ} {h u : Profile → MeridC} {a m : ℕ} {K : ℝ}
    (hu : IsDer c σ H1 h a m K u) : IsDer c σ H1 h a (m + 1) K (pdS u) where
  smooth := contDiff_pdS hu.smooth
  periodic := periodic_pdS hu.periodic
  support_s := support_s_pdS hu.support_s
  bound n p := by
    have h1 := norm_iteratedFDeriv_pdS_le hu.smooth n p
    have h2 := hu.bound (n + 1) p
    rw [show n + 1 + m = n + (m + 1) by omega] at h2
    exact h1.trans h2

theorem IsDer.add {c σ H1 : ℝ} {h u v : Profile → MeridC} {a m : ℕ} {K1 K2 : ℝ}
    (hu : IsDer c σ H1 h a m K1 u) (hv : IsDer c σ H1 h a m K2 v) :
    IsDer c σ H1 h a m (K1 + K2) (u + v) where
  smooth := hu.smooth.add hv.smooth
  periodic p := by
    simp only [Pi.add_apply]
    rw [hu.periodic p, hv.periodic p]
  support_s p hp := by simp [hu.support_s p hp, hv.support_s p hp]
  bound n p := by
    have hcu : ContDiffAt ℝ n u p :=
      (hu.smooth.of_le (by exact_mod_cast le_top)).contDiffAt
    have hcv : ContDiffAt ℝ n v p :=
      (hv.smooth.of_le (by exact_mod_cast le_top)).contDiffAt
    rw [iteratedFDeriv_add_apply hcu hcv]
    calc ‖iteratedFDeriv ℝ n u p + iteratedFDeriv ℝ n v p‖
        ≤ ‖iteratedFDeriv ℝ n u p‖ + ‖iteratedFDeriv ℝ n v p‖ := norm_add_le _ _
      _ ≤ K1 * ‖iteratedFDeriv ℝ (n + m) (opS^[a] h) p‖ +
          K2 * ‖iteratedFDeriv ℝ (n + m) (opS^[a] h) p‖ :=
          add_le_add (hu.bound n p) (hv.bound n p)
      _ = (K1 + K2) * ‖iteratedFDeriv ℝ (n + m) (opS^[a] h) p‖ := by ring

theorem IsDer.lap {c σ H1 : ℝ} {h u : Profile → MeridC} {a m : ℕ} {K : ℝ}
    (hu : IsDer c σ H1 h a m K u) : IsDer c σ H1 h a (m + 2) (K + K) (laplaceQEta u) :=
  hu.dQ.dQ.add hu.dEta.dEta

theorem IsDer.norm_le {c σ H1 : ℝ} {h u : Profile → MeridC} {a m : ℕ} {K : ℝ}
    (hu : IsDer c σ H1 h a m K u) (p : Profile) :
    ‖u p‖ ≤ K * ‖iteratedFDeriv ℝ m (opS^[a] h) p‖ := by
  have h0 := hu.bound 0 p
  rwa [norm_iteratedFDeriv_zero, Nat.zero_add] at h0

theorem IsDer.eta_le_Bsum {c σ H1 : ℝ} {h u : Profile → MeridC} {a m : ℕ} {K : ℝ}
    (hu : IsDer c σ H1 h a m K u) (hK : 0 ≤ K) (ha : a < 2) {j : ℕ} (hj : j < 3) (hm : m < 5)
    (p : Profile) : |p.2.2| ^ j * ‖u p‖ ≤ K * Bsum h p := by
  have h1 := hu.norm_le p
  have h2 := bterm_le_Bsum h ha hj hm p
  unfold bterm at h2
  calc |p.2.2| ^ j * ‖u p‖
      ≤ |p.2.2| ^ j * (K * ‖iteratedFDeriv ℝ m (opS^[a] h) p‖) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = K * (|p.2.2| ^ j * ‖iteratedFDeriv ℝ m (opS^[a] h) p‖) := by ring
    _ ≤ K * Bsum h p := mul_le_mul_of_nonneg_left h2 hK

theorem IsDer.le_Bsum {c σ H1 : ℝ} {h u : Profile → MeridC} {a m : ℕ} {K : ℝ}
    (hu : IsDer c σ H1 h a m K u) (hK : 0 ≤ K) (ha : a < 2) (hm : m < 5) (p : Profile) :
    ‖u p‖ ≤ K * Bsum h p := by
  simpa using hu.eta_le_Bsum hK ha (j := 0) (by norm_num) hm p

/-! ### 4. Dominated inner profiles `Inner` and their causal integrals -/

/-- A smooth, periodic, band-supported profile dominated by `K * Bsum h`. -/
structure Inner (c σ H1 : ℝ) (h : Profile → MeridC) (K : ℝ) (u : Profile → MeridC) : Prop where
  smooth : ContDiff ℝ ∞ u
  periodic : QPeriodic c u
  support_s : ∀ p : Profile, p.1 < σ ∨ H1 < p.1 → u p = 0
  bound : ∀ p : Profile, ‖u p‖ ≤ K * Bsum h p

theorem IsDer.inner {c σ H1 : ℝ} {h u : Profile → MeridC} {a m : ℕ} {K : ℝ}
    (hu : IsDer c σ H1 h a m K u) (hK : 0 ≤ K) (ha : a < 2) (hm : m < 5) :
    Inner c σ H1 h K u :=
  ⟨hu.smooth, hu.periodic, hu.support_s, hu.le_Bsum hK ha hm⟩

theorem IsDer.inner_eta {c σ H1 : ℝ} {h u : Profile → MeridC} {a m : ℕ} {K : ℝ}
    (hu : IsDer c σ H1 h a m K u) (hK : 0 ≤ K) (ha : a < 2) (hm : m < 5) :
    Inner c σ H1 h K (etaMul u) where
  smooth := contDiff_etaMul hu.smooth
  periodic := periodic_etaMul hu.periodic
  support_s := support_s_etaMul hu.support_s
  bound p := by
    rw [← etaMul_one_iter, norm_etaMul_iter]
    exact hu.eta_le_Bsum hK ha (j := 1) (by norm_num) hm p

theorem IsDer.inner_eta2 {c σ H1 : ℝ} {h u : Profile → MeridC} {a m : ℕ} {K : ℝ}
    (hu : IsDer c σ H1 h a m K u) (hK : 0 ≤ K) (ha : a < 2) (hm : m < 5) :
    Inner c σ H1 h K (etaMul (etaMul u)) where
  smooth := contDiff_etaMul (contDiff_etaMul hu.smooth)
  periodic := periodic_etaMul (periodic_etaMul hu.periodic)
  support_s := support_s_etaMul (support_s_etaMul hu.support_s)
  bound p := by
    rw [← etaMul_two_iter, norm_etaMul_iter]
    exact hu.eta_le_Bsum hK ha (j := 2) (by norm_num) hm p

theorem Inner.nuS {c σ H1 ν : ℝ} {h u : Profile → MeridC} {K : ℝ}
    (hu : Inner c σ H1 h K u) (hν : 0 < ν) (hσ : 0 < σ) (hσH1 : σ ≤ H1) :
    Inner c σ H1 h (ν * H1 * K) (nuSMul ν 1 u) where
  smooth := contDiff_nuSMul ν 1 hu.smooth
  periodic := periodic_nuSMul ν 1 hu.periodic
  support_s := support_s_nuSMul ν 1 hu.support_s
  bound p := by
    have h1 := norm_nuSMul_le_of_support_s hν hσ 1 hu.support_s p
    rw [pow_one] at h1
    have hY : 0 ≤ ν * H1 := (mul_pos hν (hσ.trans_le hσH1)).le
    calc ‖nuSMul ν 1 u p‖ ≤ ν * H1 * ‖u p‖ := h1
      _ ≤ ν * H1 * (K * Bsum h p) := mul_le_mul_of_nonneg_left (hu.bound p) hY
      _ = ν * H1 * K * Bsum h p := by ring

theorem IsDer.inner_eta_nuSMul {c σ H1 ν : ℝ} {h u : Profile → MeridC} {a m : ℕ} {K : ℝ}
    (hu : IsDer c σ H1 h a m K u) (hK : 0 ≤ K) (ha : a < 2) (hm : m < 5)
    (hν : 0 < ν) (hσ : 0 < σ) (hσH1 : σ ≤ H1) :
    Inner c σ H1 h (ν * H1 * K) (etaMul (nuSMul ν 1 u)) where
  smooth := contDiff_etaMul (contDiff_nuSMul ν 1 hu.smooth)
  periodic := periodic_etaMul (periodic_nuSMul ν 1 hu.periodic)
  support_s := support_s_etaMul (support_s_nuSMul ν 1 hu.support_s)
  bound p := by
    have h1 := norm_nuSMul_le_of_support_s hν hσ 1 hu.support_s p
    rw [pow_one] at h1
    have hY : 0 ≤ ν * H1 := (mul_pos hν (hσ.trans_le hσH1)).le
    have h2 := hu.eta_le_Bsum hK ha (j := 1) (by norm_num) hm p
    rw [← etaMul_one_iter, norm_etaMul_iter]
    calc |p.2.2| ^ 1 * ‖nuSMul ν 1 u p‖ ≤ |p.2.2| ^ 1 * (ν * H1 * ‖u p‖) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = ν * H1 * (|p.2.2| ^ 1 * ‖u p‖) := by ring
      _ ≤ ν * H1 * (K * Bsum h p) := mul_le_mul_of_nonneg_left h2 hY
      _ = ν * H1 * K * Bsum h p := by ring

theorem Inner.add {c σ H1 : ℝ} {h u v : Profile → MeridC} {K1 K2 : ℝ}
    (hu : Inner c σ H1 h K1 u) (hv : Inner c σ H1 h K2 v) :
    Inner c σ H1 h (K1 + K2) (u + v) where
  smooth := hu.smooth.add hv.smooth
  periodic p := by
    simp only [Pi.add_apply]
    rw [hu.periodic p, hv.periodic p]
  support_s p hp := by simp [hu.support_s p hp, hv.support_s p hp]
  bound p := by
    calc ‖(u + v) p‖ ≤ ‖u p‖ + ‖v p‖ := norm_add_le _ _
      _ ≤ K1 * Bsum h p + K2 * Bsum h p := add_le_add (hu.bound p) (hv.bound p)
      _ = (K1 + K2) * Bsum h p := by ring

theorem Inner.congr {c σ H1 : ℝ} {h u v : Profile → MeridC} {K : ℝ}
    (hu : Inner c σ H1 h K u) (huv : u = v) : Inner c σ H1 h K v := huv ▸ hu

theorem Inner.bdd {c σ H1 : ℝ} {h u : Profile → MeridC} {K : ℝ}
    (hu : Inner c σ H1 h K u) (hh : IsFlatLerayRep c σ H1 h) (hK : 0 ≤ K) :
    ∃ M : ℝ, ∀ q, ‖u q‖ ≤ M := by
  obtain ⟨MB, hMB⟩ := Bsum_bdd hh
  exact ⟨K * MB, fun q => (hu.bound q).trans (mul_le_mul_of_nonneg_left (hMB q) hK)⟩

theorem Inner.causal {c σ H1 ν γs K : ℝ} {μ : ℂ} {h u : Profile → MeridC}
    (hu : Inner c σ H1 h K u) (hh : IsFlatLerayRep c σ H1 h) (hc : 0 < c) (hγs : 0 < γs)
    (hμγ : γs ≤ μ.re + 1 / 4) (hK : 0 ≤ K) (k : ℕ) :
    L2B c (causalAdjointRep ν μ (thetaWeight k) u) (γs⁻¹ * (K * flatProjMomentNorm c h)) := by
  obtain ⟨hU, bU⟩ := L2B_of_le_Bsum hh hu.smooth.continuous.aestronglyMeasurable hK hu.bound
  exact ⟨memLp_causalAdjointRep hc ν (hγs.trans_le hμγ) (continuous_thetaWeight k)
      (norm_thetaWeight_le k) hu.smooth.continuous.stronglyMeasurable hu.periodic hU,
    (norm_causalAdjointRep_le hc ν hγs hμγ (continuous_thetaWeight k) (norm_thetaWeight_le k)
      hu.smooth.continuous.stronglyMeasurable hu.periodic hU).trans
      (mul_le_mul_of_nonneg_left bU (inv_nonneg.2 hγs.le))⟩

theorem Inner.causal_zero {c σ H1 ν K : ℝ} {μ : ℂ} {h u : Profile → MeridC}
    (hu : Inner c σ H1 h K u) (hσ : 0 < σ) (hσH1 : σ ≤ H1) (Φ : ℝ → ℂ) {p : Profile}
    (hp : H1 < p.1) : causalAdjointRep ν μ Φ u p = 0 :=
  causalAdjointRep_eq_zero_of_support_s hσ hσH1 ν μ Φ hu.support_s hp

/-! ### 5. The multiplier `ν s` against `∂_q`, `∂_η`, `Δ`; `IsDiffProfile` for `ν s w` -/

theorem fderiv_nuSMul_one_apply (ν : ℝ) {f : Profile → MeridC} {p : Profile}
    (hf : DifferentiableAt ℝ f p) (v : Profile) :
    fderiv ℝ (nuSMul ν 1 f) p v = (ν * p.1) • fderiv ℝ f p v + (ν * v.1) • f p := by
  have hfun : nuSMul ν 1 f = (fun q : Profile => ν * q.1) • f :=
    funext (nuSMul_one_apply ν f)
  have hfst : HasFDerivAt (fun q : Profile => ν * q.1)
      (ν • ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)) p :=
    ((ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).hasFDerivAt).const_mul ν
  have hsmul := hfst.smul hf.hasFDerivAt
  rw [hfun, hsmul.fderiv]
  simp

theorem pdQ_nuSMul_one (ν : ℝ) {f : Profile → MeridC} (hf : Differentiable ℝ f) :
    pdQ (nuSMul ν 1 f) = nuSMul ν 1 (pdQ f) := by
  funext p
  rw [nuSMul_one_apply]
  show fderiv ℝ (nuSMul ν 1 f) p (0, 1, 0) = (ν * p.1) • fderiv ℝ f p (0, 1, 0)
  rw [fderiv_nuSMul_one_apply ν (hf p)]
  simp

theorem pdEta_nuSMul_one (ν : ℝ) {f : Profile → MeridC} (hf : Differentiable ℝ f) :
    pdEta (nuSMul ν 1 f) = nuSMul ν 1 (pdEta f) := by
  funext p
  rw [nuSMul_one_apply]
  show fderiv ℝ (nuSMul ν 1 f) p (0, 0, 1) = (ν * p.1) • fderiv ℝ f p (0, 0, 1)
  rw [fderiv_nuSMul_one_apply ν (hf p)]
  simp

theorem laplaceQEta_nuSMul_one (ν : ℝ) {f : Profile → MeridC} (hf : ContDiff ℝ ∞ f) :
    laplaceQEta (nuSMul ν 1 f) = nuSMul ν 1 (laplaceQEta f) := by
  have h1 := pdQ_nuSMul_one ν (hf.differentiable (by simp))
  have h2 := pdQ_nuSMul_one ν ((contDiff_pdQ hf).differentiable (by simp))
  have h3 := pdEta_nuSMul_one ν (hf.differentiable (by simp))
  have h4 := pdEta_nuSMul_one ν ((contDiff_pdEta hf).differentiable (by simp))
  funext p
  simp only [laplaceQEta, h1, h2, h3, h4]
  rw [nuSMul_one_apply, nuSMul_one_apply, nuSMul_one_apply]
  show _ = (ν * p.1) • (pdQ (pdQ f) p + pdEta (pdEta f) p)
  rw [smul_add]

theorem norm_opS_le_of_support {σ H1 : ℝ} (hσ : 0 < σ) (hσH1 : σ ≤ H1) {w : Profile → MeridC}
    (hw : ∀ p : Profile, p.1 < σ ∨ H1 < p.1 → w p = 0) (p : Profile) :
    ‖opS w p‖ ≤ H1 * ‖pdS w p‖ := by
  by_cases hp : p.1 < σ ∨ H1 < p.1
  · rw [support_s_opS hw p hp, norm_zero]
    exact mul_nonneg (hσ.le.trans hσH1) (norm_nonneg _)
  · rw [not_or, not_lt, not_lt] at hp
    show ‖p.1 • pdS w p‖ ≤ H1 * ‖pdS w p‖
    rw [norm_smul, Real.norm_of_nonneg (hσ.le.trans hp.1)]
    exact mul_le_mul_of_nonneg_right hp.2 (norm_nonneg _)

theorem IsDer.isDiffProfile {c σ H1 : ℝ} {h u : Profile → MeridC} {a m : ℕ} {K : ℝ}
    (hu : IsDer c σ H1 h a m K u) (hh : IsFlatLerayRep c σ H1 h) (hσ : 0 < σ) (hσH1 : σ ≤ H1)
    (hK : 0 ≤ K) (ha : a < 2) (hm : m + 2 < 5) : IsDiffProfile σ H1 u where
  smooth := hu.smooth
  support_s := hu.support_s
  bdd_w := (hu.inner hK ha (by omega)).bdd hh hK
  bdd_opS := by
    obtain ⟨M, hM⟩ := (hu.dS.inner hK ha (by omega)).bdd hh hK
    exact ⟨H1 * M, fun q => (norm_opS_le_of_support hσ hσH1 hu.support_s q).trans
      (mul_le_mul_of_nonneg_left (hM q) (hσ.le.trans hσH1))⟩
  bdd_pdQ := (hu.dQ.inner hK ha (by omega)).bdd hh hK
  bdd_pdQ2 := (hu.dQ.dQ.inner hK ha (by omega)).bdd hh hK
  bdd_pdEta := (hu.dEta.inner hK ha (by omega)).bdd hh hK
  bdd_pdEta2 := (hu.dEta.dEta.inner hK ha (by omega)).bdd hh hK

theorem IsDiffProfile.nuSMul_one {σ H1 ν : ℝ} (hν : 0 < ν) (hσ : 0 < σ) (hσH1 : σ ≤ H1)
    {w : Profile → MeridC} (hw : IsDiffProfile σ H1 w) : IsDiffProfile σ H1 (nuSMul ν 1 w) where
  smooth := contDiff_nuSMul ν 1 hw.smooth
  support_s := support_s_nuSMul ν 1 hw.support_s
  bdd_w := bdd_nuSMul_of_support_s hν hσ hσH1 1 hw.support_s hw.bdd_w
  bdd_opS := by
    obtain ⟨M1, h1⟩ := bdd_nuSMul_of_support_s hν hσ hσH1 1 hw.support_s hw.bdd_w
    obtain ⟨M2, h2⟩ := bdd_nuSMul_of_support_s hν hσ hσH1 1 (support_s_opS hw.support_s)
      hw.bdd_opS
    refine ⟨M1 + M2, fun q => ?_⟩
    rw [opS_nuSMul_one_eq ν hw.smooth]
    exact (norm_add_le _ _).trans (add_le_add (h1 q) (h2 q))
  bdd_pdQ := by
    rw [pdQ_nuSMul_one ν (hw.smooth.differentiable (by simp))]
    exact bdd_nuSMul_of_support_s hν hσ hσH1 1 (support_s_pdQ hw.support_s) hw.bdd_pdQ
  bdd_pdQ2 := by
    rw [pdQ_nuSMul_one ν (hw.smooth.differentiable (by simp)),
      pdQ_nuSMul_one ν ((contDiff_pdQ hw.smooth).differentiable (by simp))]
    exact bdd_nuSMul_of_support_s hν hσ hσH1 1 (support_s_pdQ (support_s_pdQ hw.support_s))
      hw.bdd_pdQ2
  bdd_pdEta := by
    rw [pdEta_nuSMul_one ν (hw.smooth.differentiable (by simp))]
    exact bdd_nuSMul_of_support_s hν hσ hσH1 1 (support_s_pdEta hw.support_s) hw.bdd_pdEta
  bdd_pdEta2 := by
    rw [pdEta_nuSMul_one ν (hw.smooth.differentiable (by simp)),
      pdEta_nuSMul_one ν ((contDiff_pdEta hw.smooth).differentiable (by simp))]
    exact bdd_nuSMul_of_support_s hν hσ hσH1 1 (support_s_pdEta (support_s_pdEta hw.support_s))
      hw.bdd_pdEta2

/-! ### 6. Derivatives of locally equal profiles -/

theorem opS_congr_nhds {f g : Profile → MeridC} {p : Profile} (hfg : f =ᶠ[𝓝 p] g) :
    opS f p = opS g p := by
  show p.1 • fderiv ℝ f p (1, 0, 0) = p.1 • fderiv ℝ g p (1, 0, 0)
  rw [hfg.fderiv_eq]

theorem pdEta_congr_nhds {f g : Profile → MeridC} {p : Profile} (hfg : f =ᶠ[𝓝 p] g) :
    pdEta f p = pdEta g p := by
  show fderiv ℝ f p (0, 0, 1) = fderiv ℝ g p (0, 0, 1)
  rw [hfg.fderiv_eq]

theorem opS_add_apply {f g : Profile → MeridC} {p : Profile} (hf : DifferentiableAt ℝ f p)
    (hg : DifferentiableAt ℝ g p) : opS (f + g) p = opS f p + opS g p := by
  show p.1 • fderiv ℝ (f + g) p (1, 0, 0) =
    p.1 • fderiv ℝ f p (1, 0, 0) + p.1 • fderiv ℝ g p (1, 0, 0)
  rw [fderiv_add hf hg, ContinuousLinearMap.add_apply, smul_add]

/-- The open half-space `{s > 0}` is a neighbourhood of each of its points. -/
theorem pos_mem_nhds {p : Profile} (hp : 0 < p.1) : {q : Profile | 0 < q.1} ∈ 𝓝 p :=
  (isOpen_lt continuous_const continuous_fst).mem_nhds hp

/-! ### 7. Polynomial `GammaBox` arithmetic -/

theorem gammaBox_facts {ν c σ H1 L1 M γs : ℝ} (hc : 0 < c) (hν : 0 < ν) (hσ : 0 < σ)
    (hσH1 : σ ≤ H1) (hL1 : 0 ≤ L1) (hM : 0 ≤ M) (hγs : 0 < γs) :
    1 ≤ GammaBox ν c σ H1 L1 M γs ∧ γs⁻¹ ≤ GammaBox ν c σ H1 L1 M γs ∧
      H1 ≤ GammaBox ν c σ H1 L1 M γs ∧ ν * H1 ≤ GammaBox ν c σ H1 L1 M γs ^ 2 := by
  have hH1 : 0 < H1 := hσ.trans_le hσH1
  have hG1 := one_le_GammaBox hν hc hσ hσH1 hL1 hM hγs
  have hγG := inv_gammas_le_GammaBox ν c σ H1 L1 M γs hν hc hσ hσH1 hL1 hM
  have h1 : 0 ≤ ν⁻¹ := inv_nonneg.2 hν.le
  have h2 : 0 ≤ c⁻¹ := inv_nonneg.2 hc.le
  have h3 : 0 ≤ σ⁻¹ := inv_nonneg.2 hσ.le
  have h4 : 0 ≤ γs⁻¹ := inv_nonneg.2 hγs.le
  have hνG : ν ≤ GammaBox ν c σ H1 L1 M γs := by unfold GammaBox; linarith
  have hHG : H1 ≤ GammaBox ν c σ H1 L1 M γs := by unfold GammaBox; linarith
  refine ⟨hG1, hγG, hHG, ?_⟩
  rw [sq]
  exact mul_le_mul hνG hHG hH1.le (zero_le_one.trans hG1)

theorem poly_le {G Y g F : ℝ} (hG1 : 1 ≤ G) (hY0 : 0 ≤ Y) (hY : Y ≤ G ^ 2) (hg0 : 0 ≤ g)
    (hg : g ≤ G) (hF : 0 ≤ F) {a b d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hd : 0 ≤ d) :
    Y * g * F * (a + b * Y + d * Y ^ 2) ≤ (a + b + d) * G ^ 7 * F := by
  have hG0 : 0 ≤ G := zero_le_one.trans hG1
  have h1 : Y * g ≤ G ^ 3 := by
    calc Y * g ≤ G ^ 2 * G := mul_le_mul hY hg hg0 (by positivity)
      _ = G ^ 3 := by ring
  have hG4 : 1 ≤ G ^ 4 := one_le_pow₀ hG1
  have hY4 : Y ≤ G ^ 4 := hY.trans (pow_le_pow_right₀ hG1 (by norm_num))
  have hYY : Y ^ 2 ≤ G ^ 4 := by
    calc Y ^ 2 ≤ (G ^ 2) ^ 2 := pow_le_pow_left₀ hY0 hY 2
      _ = G ^ 4 := by ring
  have h2 : a + b * Y + d * Y ^ 2 ≤ (a + b + d) * G ^ 4 := by
    have e1 : a ≤ a * G ^ 4 := le_mul_of_one_le_right ha hG4
    have e2 : b * Y ≤ b * G ^ 4 := mul_le_mul_of_nonneg_left hY4 hb
    have e3 : d * Y ^ 2 ≤ d * G ^ 4 := mul_le_mul_of_nonneg_left hYY hd
    nlinarith
  have hP : 0 ≤ a + b * Y + d * Y ^ 2 := by positivity
  calc Y * g * F * (a + b * Y + d * Y ^ 2) = (Y * g) * (a + b * Y + d * Y ^ 2) * F := by ring
    _ ≤ G ^ 3 * ((a + b + d) * G ^ 4) * F := by
        gcongr
    _ = (a + b + d) * G ^ 7 * F := by ring

end Gen2Aux

end UnforcedLeray.Short.PartIIa
